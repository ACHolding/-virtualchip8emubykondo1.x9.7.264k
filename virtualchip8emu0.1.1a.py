#!/usr/bin/env python3
"""
CHIP-8 Emulator with mGBA-style GUI  --  v0.1.2 (bugfix pass)
Cross-platform (Windows, macOS, Linux). tkinter + stdlib only. No assets.

CHANGES vs 0.1.1
  * AUDIO IS OFF. No os.system('beep'), no winsound, no shell out. The sound
    timer is still emulated exactly (ROMs that poll ST behave correctly), it
    just drives a silent on-screen indicator instead of a subprocess.
    Optional Tk bell can be enabled from the Emulation menu (off by default,
    and rate-limited to one ping per ST rising edge, never per frame).
  * Font table now lives in Chip8.reset() so it survives every reset/load.
  * PC / I / BCD / sprite fetch all masked to 0xFFF -- no more IndexError at
    the top of RAM.
  * VF is written AFTER Vx in 8xy4/5/6/7/E, so opcodes targeting VF are right.
  * DRW now clips at the screen edge (only the start coord wraps) -- the old
    full-wrap version corrupted the display in most games.
  * Fx0A waits for key RELEASE, like real hardware.
  * Stack capped at 16 frames; RET on empty stack no longer silently falls
    through into garbage.
  * Renderer: reuses one zoomed PhotoImage via Tk's `copy -zoom` instead of
    allocating a new image every frame. Big speedup, no GC churn.
  * FPS counter seeded from a real clock (no bogus first reading), frame loop
    is drift-compensated toward a true 60 Hz.
  * Keys read from event.keysym, so modifiers/caps-lock don't break input.
  * Manual zoom no longer gets stomped by the next window resize.
  * Configurable quirks (VF-reset, shift, load/store I increment, BNNN).
"""

import os
import time
import random
import tkinter as tk
from tkinter import filedialog, messagebox

# =============================================================================
# Constants
# =============================================================================
SCREEN_W, SCREEN_H = 64, 32
MEM_SIZE = 4096
PROGRAM_START = 0x200
FONT_START = 0x50
STACK_LIMIT = 16
TARGET_FPS = 60.0

COLOR_ON = '#FFFFFF'
COLOR_OFF = '#000000'
BG_DARK = '#1e1e1e'
BG_PANEL = '#2b2b2b'
FG_TEXT = '#d4d4d4'

FONT_DATA = (
    0xF0, 0x90, 0x90, 0x90, 0xF0,  # 0
    0x20, 0x60, 0x20, 0x20, 0x70,  # 1
    0xF0, 0x10, 0xF0, 0x80, 0xF0,  # 2
    0xF0, 0x10, 0xF0, 0x10, 0xF0,  # 3
    0x90, 0x90, 0xF0, 0x10, 0x10,  # 4
    0xF0, 0x80, 0xF0, 0x10, 0xF0,  # 5
    0xF0, 0x80, 0xF0, 0x90, 0xF0,  # 6
    0xF0, 0x10, 0x20, 0x40, 0x40,  # 7
    0xF0, 0x90, 0xF0, 0x90, 0xF0,  # 8
    0xF0, 0x90, 0xF0, 0x10, 0xF0,  # 9
    0xF0, 0x90, 0xF0, 0x90, 0x90,  # A
    0xE0, 0x90, 0xE0, 0x90, 0xE0,  # B
    0xF0, 0x80, 0x80, 0x80, 0xF0,  # C
    0xE0, 0x90, 0x90, 0x90, 0xE0,  # D
    0xF0, 0x80, 0xF0, 0x80, 0xF0,  # E
    0xF0, 0x80, 0xF0, 0x80, 0x80,  # F
)


# =============================================================================
# CHIP-8 Emulator Core
# =============================================================================
class Chip8:
    """CHIP-8 interpreter. All standard opcodes, configurable quirks."""

    def __init__(self):
        # Quirk flags (defaults = COSMAC VIP behaviour where it matters most)
        self.quirk_vf_reset = True      # 8xy1/2/3 clear VF
        self.quirk_shift_vy = False     # 8xy6/E shift Vy into Vx (False = shift Vx)
        self.quirk_mem_increment = False  # Fx55/Fx65 leave I incremented
        self.quirk_jump_vx = False      # BNNN uses VX instead of V0
        self.rom = b''
        self.reset()

    # -- state -----------------------------------------------------------
    def reset(self):
        """Full CPU reset. Reloads font AND the current ROM if one is held."""
        self.memory = bytearray(MEM_SIZE)
        self.v = [0] * 16
        self.index = 0
        self.pc = PROGRAM_START
        self.stack = []
        self.delay_timer = 0
        self.sound_timer = 0
        self.display = [[0] * SCREEN_W for _ in range(SCREEN_H)]
        self.keys = [0] * 16
        self.draw_flag = True
        self.halted = False
        self._wait_key = None  # Fx0A latch

        # Font is part of the machine, not something the GUI bolts on after.
        self.memory[FONT_START:FONT_START + len(FONT_DATA)] = bytes(FONT_DATA)
        if self.rom:
            self._blit_rom(self.rom)

    def _blit_rom(self, data):
        end = min(len(data), MEM_SIZE - PROGRAM_START)
        self.memory[PROGRAM_START:PROGRAM_START + end] = data[:end]
        return end

    def load_rom(self, data):
        """Load ROM bytes at 0x200. Returns bytes actually loaded."""
        if not data:
            raise ValueError("ROM file is empty")
        if len(data) > MEM_SIZE - PROGRAM_START:
            # Not fatal -- just truncate, same as real hardware would ignore.
            data = data[:MEM_SIZE - PROGRAM_START]
        self.rom = bytes(data)
        self.reset()
        return len(self.rom)

    # -- cpu -------------------------------------------------------------
    def fetch_opcode(self):
        pc = self.pc & 0xFFF
        return (self.memory[pc] << 8) | self.memory[(pc + 1) & 0xFFF]

    def execute_cycle(self):
        if self.halted:
            return
        opcode = self.fetch_opcode()
        self.pc = (self.pc + 2) & 0xFFF

        nnn = opcode & 0x0FFF
        n = opcode & 0x000F
        x = (opcode & 0x0F00) >> 8
        y = (opcode & 0x00F0) >> 4
        kk = opcode & 0x00FF
        top = opcode & 0xF000

        if opcode == 0x00E0:                      # CLS
            self.display = [[0] * SCREEN_W for _ in range(SCREEN_H)]
            self.draw_flag = True

        elif opcode == 0x00EE:                    # RET
            if self.stack:
                self.pc = self.stack.pop() & 0xFFF
            else:
                self.halted = True                # stack underflow: stop, don't run wild

        elif top == 0x1000:                       # JP addr
            self.pc = nnn

        elif top == 0x2000:                       # CALL addr
            if len(self.stack) >= STACK_LIMIT:
                self.halted = True
            else:
                self.stack.append(self.pc)
                self.pc = nnn

        elif top == 0x3000:                       # SE Vx, byte
            if self.v[x] == kk:
                self.pc = (self.pc + 2) & 0xFFF

        elif top == 0x4000:                       # SNE Vx, byte
            if self.v[x] != kk:
                self.pc = (self.pc + 2) & 0xFFF

        elif top == 0x5000 and n == 0:            # SE Vx, Vy
            if self.v[x] == self.v[y]:
                self.pc = (self.pc + 2) & 0xFFF

        elif top == 0x6000:                       # LD Vx, byte
            self.v[x] = kk

        elif top == 0x7000:                       # ADD Vx, byte
            self.v[x] = (self.v[x] + kk) & 0xFF

        elif top == 0x8000:
            if n == 0x0:                          # LD Vx, Vy
                self.v[x] = self.v[y]
            elif n == 0x1:                        # OR
                self.v[x] |= self.v[y]
                if self.quirk_vf_reset:
                    self.v[0xF] = 0
            elif n == 0x2:                        # AND
                self.v[x] &= self.v[y]
                if self.quirk_vf_reset:
                    self.v[0xF] = 0
            elif n == 0x3:                        # XOR
                self.v[x] ^= self.v[y]
                if self.quirk_vf_reset:
                    self.v[0xF] = 0
            elif n == 0x4:                        # ADD Vx, Vy
                result = self.v[x] + self.v[y]
                self.v[x] = result & 0xFF
                self.v[0xF] = 1 if result > 0xFF else 0
            elif n == 0x5:                        # SUB Vx, Vy
                borrow = 1 if self.v[x] >= self.v[y] else 0
                self.v[x] = (self.v[x] - self.v[y]) & 0xFF
                self.v[0xF] = borrow
            elif n == 0x6:                        # SHR
                src = self.v[y] if self.quirk_shift_vy else self.v[x]
                flag = src & 0x1
                self.v[x] = src >> 1
                self.v[0xF] = flag
            elif n == 0x7:                        # SUBN Vx, Vy
                borrow = 1 if self.v[y] >= self.v[x] else 0
                self.v[x] = (self.v[y] - self.v[x]) & 0xFF
                self.v[0xF] = borrow
            elif n == 0xE:                        # SHL
                src = self.v[y] if self.quirk_shift_vy else self.v[x]
                flag = (src >> 7) & 0x1
                self.v[x] = (src << 1) & 0xFF
                self.v[0xF] = flag

        elif top == 0x9000 and n == 0:            # SNE Vx, Vy
            if self.v[x] != self.v[y]:
                self.pc = (self.pc + 2) & 0xFFF

        elif top == 0xA000:                       # LD I, addr
            self.index = nnn

        elif top == 0xB000:                       # JP V0, addr (or Vx quirk)
            base = self.v[x] if self.quirk_jump_vx else self.v[0]
            self.pc = (nnn + base) & 0xFFF

        elif top == 0xC000:                       # RND Vx, byte
            self.v[x] = random.getrandbits(8) & kk

        elif top == 0xD000:                       # DRW Vx, Vy, nibble
            self._draw_sprite(self.v[x], self.v[y], n)

        elif top == 0xE000:
            key = self.v[x] & 0xF
            if kk == 0x9E:                        # SKP Vx
                if self.keys[key]:
                    self.pc = (self.pc + 2) & 0xFFF
            elif kk == 0xA1:                      # SKNP Vx
                if not self.keys[key]:
                    self.pc = (self.pc + 2) & 0xFFF

        elif top == 0xF000:
            if kk == 0x07:                        # LD Vx, DT
                self.v[x] = self.delay_timer
            elif kk == 0x0A:                      # LD Vx, K -- wait for release
                if self._wait_key is None:
                    for i in range(16):
                        if self.keys[i]:
                            self._wait_key = i
                            break
                    self.pc = (self.pc - 2) & 0xFFF
                elif self.keys[self._wait_key]:
                    self.pc = (self.pc - 2) & 0xFFF
                else:
                    self.v[x] = self._wait_key
                    self._wait_key = None
            elif kk == 0x15:                      # LD DT, Vx
                self.delay_timer = self.v[x]
            elif kk == 0x18:                      # LD ST, Vx
                self.sound_timer = self.v[x]
            elif kk == 0x1E:                      # ADD I, Vx
                self.index = (self.index + self.v[x]) & 0xFFF
            elif kk == 0x29:                      # LD F, Vx
                self.index = (FONT_START + (self.v[x] & 0xF) * 5) & 0xFFF
            elif kk == 0x33:                      # BCD
                value = self.v[x]
                i = self.index
                self.memory[i & 0xFFF] = value // 100
                self.memory[(i + 1) & 0xFFF] = (value // 10) % 10
                self.memory[(i + 2) & 0xFFF] = value % 10
            elif kk == 0x55:                      # LD [I], Vx
                for i in range(x + 1):
                    self.memory[(self.index + i) & 0xFFF] = self.v[i]
                if self.quirk_mem_increment:
                    self.index = (self.index + x + 1) & 0xFFF
            elif kk == 0x65:                      # LD Vx, [I]
                for i in range(x + 1):
                    self.v[i] = self.memory[(self.index + i) & 0xFFF]
                if self.quirk_mem_increment:
                    self.index = (self.index + x + 1) & 0xFFF
        # anything else: unknown opcode, treated as NOP

    def _draw_sprite(self, vx, vy, height):
        """XOR sprite to screen. Start coord wraps; the sprite body CLIPS."""
        x0 = vx % SCREEN_W
        y0 = vy % SCREEN_H
        collision = 0
        for row in range(height):
            py = y0 + row
            if py >= SCREEN_H:
                break
            byte = self.memory[(self.index + row) & 0xFFF]
            if byte == 0:
                continue
            line = self.display[py]
            for col in range(8):
                if not (byte & (0x80 >> col)):
                    continue
                px = x0 + col
                if px >= SCREEN_W:
                    break
                if line[px]:
                    line[px] = 0
                    collision = 1
                else:
                    line[px] = 1
        self.v[0xF] = collision
        self.draw_flag = True

    def decrement_timers(self):
        """60 Hz tick. Returns True on the frame the sound timer starts."""
        if self.delay_timer > 0:
            self.delay_timer -= 1
        if self.sound_timer > 0:
            self.sound_timer -= 1


# =============================================================================
# mGBA-style GUI
# =============================================================================
class Chip8EmulatorGUI:
    """Main window: menu, scaled framebuffer, status bar."""

    # keysym -> CHIP-8 keypad nibble
    KEY_MAP = {
        '1': 0x1, '2': 0x2, '3': 0x3, '4': 0xC,
        'q': 0x4, 'w': 0x5, 'e': 0x6, 'r': 0xD,
        'a': 0x7, 's': 0x8, 'd': 0x9, 'f': 0xE,
        'z': 0xA, 'x': 0x0, 'c': 0xB, 'v': 0xF,
    }

    def __init__(self, root):
        self.root = root
        self.root.title("CHIP-8 Emulator")
        self.root.configure(bg=BG_DARK)
        self.root.geometry("660x400")
        self.root.minsize(320, 200)

        self.chip8 = Chip8()

        # State
        self.rom_loaded = False
        self.rom_name = "No ROM loaded"
        self.paused = False
        self.fps = 0.0
        self.frame_count = 0
        self.last_fps_update = time.perf_counter()
        self.cycles_per_frame = 12          # ~720 Hz at 60 FPS
        self.zoom = 10
        self.fit_to_window = True
        self._after_id = None
        self._next_frame = time.perf_counter()
        self._prev_sound = 0

        self._create_menu()
        self._create_display()
        self._create_status_bar()
        self._bind_keys()

        self.root.protocol("WM_DELETE_WINDOW", self._on_close)
        self._update_status()
        self._update_loop()

    # -- construction -----------------------------------------------------
    def _create_menu(self):
        menubar = tk.Menu(self.root)

        file_menu = tk.Menu(menubar, tearoff=0)
        file_menu.add_command(label="Open ROM...", command=self.load_rom, accelerator="Ctrl+O")
        file_menu.add_separator()
        file_menu.add_command(label="Exit", command=self._on_close)
        menubar.add_cascade(label="File", menu=file_menu)

        emu_menu = tk.Menu(menubar, tearoff=0)
        emu_menu.add_command(label="Pause/Resume", command=self.toggle_pause, accelerator="P")
        emu_menu.add_command(label="Reset", command=self.reset_emulator, accelerator="Ctrl+R")
        emu_menu.add_separator()
        self.speed_var = tk.IntVar(value=self.cycles_per_frame)
        for cycles in (7, 12, 16, 20, 30, 60):
            emu_menu.add_radiobutton(
                label=f"Speed: {cycles} cycles/frame  (~{cycles * 60} Hz)",
                variable=self.speed_var, value=cycles,
                command=lambda c=cycles: self.set_speed(c))
        emu_menu.add_separator()
        # Audio: silent by default. No subprocesses, ever.
        self.bell_var = tk.BooleanVar(value=False)
        emu_menu.add_checkbutton(label="Tk bell on sound timer (off)",
                                 variable=self.bell_var)
        menubar.add_cascade(label="Emulation", menu=emu_menu)

        quirks = tk.Menu(menubar, tearoff=0)
        self.q_vf = tk.BooleanVar(value=self.chip8.quirk_vf_reset)
        self.q_shift = tk.BooleanVar(value=self.chip8.quirk_shift_vy)
        self.q_mem = tk.BooleanVar(value=self.chip8.quirk_mem_increment)
        self.q_jump = tk.BooleanVar(value=self.chip8.quirk_jump_vx)
        quirks.add_checkbutton(label="8xy1/2/3 reset VF", variable=self.q_vf,
                               command=self._apply_quirks)
        quirks.add_checkbutton(label="8xy6/E shift Vy", variable=self.q_shift,
                               command=self._apply_quirks)
        quirks.add_checkbutton(label="Fx55/65 increment I", variable=self.q_mem,
                               command=self._apply_quirks)
        quirks.add_checkbutton(label="BNNN jumps with Vx", variable=self.q_jump,
                               command=self._apply_quirks)
        menubar.add_cascade(label="Quirks", menu=quirks)

        view_menu = tk.Menu(menubar, tearoff=0)
        view_menu.add_command(label="Zoom In", command=lambda: self.change_zoom(2), accelerator="Ctrl++")
        view_menu.add_command(label="Zoom Out", command=lambda: self.change_zoom(-2), accelerator="Ctrl+-")
        view_menu.add_command(label="Fit to Window", command=lambda: self.change_zoom(0), accelerator="Ctrl+0")
        menubar.add_cascade(label="View", menu=view_menu)

        help_menu = tk.Menu(menubar, tearoff=0)
        help_menu.add_command(label="Controls", command=self.show_controls)
        help_menu.add_command(label="About", command=self.show_about)
        menubar.add_cascade(label="Help", menu=help_menu)

        self.root.config(menu=menubar)

    def _create_display(self):
        self.display_frame = tk.Frame(self.root, bg=BG_PANEL)
        self.display_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        self.canvas = tk.Canvas(self.display_frame, bg=COLOR_OFF, highlightthickness=0)
        self.canvas.pack(fill=tk.BOTH, expand=True)

        # Native 64x32 framebuffer image + a separate zoomed image we reuse.
        self.photo = tk.PhotoImage(width=SCREEN_W, height=SCREEN_H)
        self.display_photo = tk.PhotoImage(width=SCREEN_W * self.zoom,
                                           height=SCREEN_H * self.zoom)
        self._photo_zoom = self.zoom
        self.canvas_image = self.canvas.create_image(0, 0, image=self.display_photo,
                                                     anchor=tk.NW)
        self.display_frame.bind("<Configure>", self._on_resize)
        self._redraw_display()

    def _create_status_bar(self):
        status_frame = tk.Frame(self.root, bg=BG_DARK)
        status_frame.pack(fill=tk.X, side=tk.BOTTOM)
        self.status_var = tk.StringVar(value="No ROM loaded | FPS: 0.0 | Stopped")
        tk.Label(status_frame, textvariable=self.status_var, bg=BG_DARK, fg=FG_TEXT,
                 anchor=tk.W, padx=5, pady=2).pack(fill=tk.X)

    def _bind_keys(self):
        self.root.bind('<KeyPress>', self._key_press)
        self.root.bind('<KeyRelease>', self._key_release)
        self.root.bind('<Control-o>', lambda e: self.load_rom())
        self.root.bind('<Control-r>', lambda e: self.reset_emulator())
        self.root.bind('<Control-plus>', lambda e: self.change_zoom(2))
        self.root.bind('<Control-equal>', lambda e: self.change_zoom(2))   # macOS-friendly
        self.root.bind('<Control-minus>', lambda e: self.change_zoom(-2))
        self.root.bind('<Control-0>', lambda e: self.change_zoom(0))

    # -- input -------------------------------------------------------------
    def _key_press(self, event):
        key = event.keysym.lower()
        if key == 'p':
            self.toggle_pause()
            return
        idx = self.KEY_MAP.get(key)
        if idx is not None:
            self.chip8.keys[idx] = 1

    def _key_release(self, event):
        idx = self.KEY_MAP.get(event.keysym.lower())
        if idx is not None:
            self.chip8.keys[idx] = 0

    def _apply_quirks(self):
        self.chip8.quirk_vf_reset = self.q_vf.get()
        self.chip8.quirk_shift_vy = self.q_shift.get()
        self.chip8.quirk_mem_increment = self.q_mem.get()
        self.chip8.quirk_jump_vx = self.q_jump.get()

    # -- video -------------------------------------------------------------
    def _on_resize(self, event):
        if not self.fit_to_window:
            return
        scale = int(min(event.width / SCREEN_W, event.height / SCREEN_H))
        scale = max(1, min(32, scale))
        if scale != self.zoom:
            self.zoom = scale
        self._redraw_display()

    def change_zoom(self, delta):
        if delta == 0:
            self.fit_to_window = True
            w = self.display_frame.winfo_width() or SCREEN_W * 10
            h = self.display_frame.winfo_height() or SCREEN_H * 10
            self.zoom = max(1, min(32, int(min(w / SCREEN_W, h / SCREEN_H))))
        else:
            self.fit_to_window = False
            self.zoom = max(1, min(32, self.zoom + delta))
        self._redraw_display()

    def _redraw_display(self):
        # Build one Tcl-style row string: {#fff #000 ...} {...}
        rows = []
        for fb_row in self.chip8.display:
            rows.append('{' + ' '.join(COLOR_ON if p else COLOR_OFF for p in fb_row) + '}')
        self.photo.put(' '.join(rows))

        zoom = max(1, self.zoom)
        # Canvas.scale() does NOT magnify pixel data, and PhotoImage.zoom()
        # allocates a fresh image every call. Reuse one destination image and
        # blit into it with Tk's `copy -zoom` instead.
        if zoom != self._photo_zoom:
            self.display_photo = tk.PhotoImage(width=SCREEN_W * zoom,
                                               height=SCREEN_H * zoom)
            self.canvas.itemconfig(self.canvas_image, image=self.display_photo)
            self._photo_zoom = zoom
        self.display_photo.tk.call(self.display_photo, 'copy', self.photo,
                                   '-zoom', zoom, zoom)

        w = self.display_frame.winfo_width()
        h = self.display_frame.winfo_height()
        x_off = max(0, (w - SCREEN_W * zoom) // 2)
        y_off = max(0, (h - SCREEN_H * zoom) // 2)
        self.canvas.coords(self.canvas_image, x_off, y_off)

    # -- control -----------------------------------------------------------
    def load_rom(self):
        filename = filedialog.askopenfilename(
            title="Open CHIP-8 ROM",
            filetypes=[("CHIP-8 ROMs", "*.ch8 *.c8 *.rom *.bin"), ("All files", "*.*")])
        if not filename:
            return
        try:
            with open(filename, 'rb') as f:
                data = f.read()
            self.chip8.load_rom(data)      # reset() reloads font + ROM itself
            self.rom_loaded = True
            self.rom_name = os.path.basename(filename)
            self.paused = False
            self._update_status()
            self._redraw_display()
        except Exception as e:
            messagebox.showerror("Error", f"Failed to load ROM:\n{e}")

    def toggle_pause(self):
        if not self.rom_loaded:
            return
        self.paused = not self.paused
        self._update_status()

    def reset_emulator(self):
        self.chip8.reset()               # font + held ROM come back automatically
        self.paused = False
        self._update_status()
        self._redraw_display()

    def set_speed(self, cycles):
        self.cycles_per_frame = cycles
        self.speed_var.set(cycles)
        self._update_status()

    # -- status / help -----------------------------------------------------
    def _update_status(self):
        if not self.rom_loaded:
            state = "Stopped"
        elif self.chip8.halted:
            state = "Halted"
        elif self.paused:
            state = "Paused"
        else:
            state = "Running"
        snd = " ♪" if self.chip8.sound_timer > 0 else ""
        self.status_var.set(
            f"{self.rom_name} | FPS: {self.fps:.1f} | {state} | "
            f"Cycles/frame: {self.cycles_per_frame} | Zoom: {self.zoom}x{snd}")

    def show_controls(self):
        messagebox.showinfo("Controls", """CHIP-8 Keyboard Mapping:

CHIP-8 Keypad        PC Keyboard
1 2 3 C              1 2 3 4
4 5 6 D              Q W E R
7 8 9 E              A S D F
A 0 B F              Z X C V

Other keys:
P          Pause/Resume
Ctrl+O     Open ROM
Ctrl+R     Reset
Ctrl++     Zoom In
Ctrl+-     Zoom Out
Ctrl+0     Fit to Window
""")

    def show_about(self):
        messagebox.showinfo("About", """CHIP-8 Emulator  v0.1.2

tkinter + stdlib only. Single file, no assets.
Audio is silent by design -- the sound timer drives an
on-screen indicator, never a shell command.

Quirks menu lets you match COSMAC VIP or SUPER-CHIP
behaviour per-ROM.
""")

    # -- main loop ---------------------------------------------------------
    def _update_loop(self):
        if self.rom_loaded and not self.paused and not self.chip8.halted:
            chip = self.chip8
            for _ in range(self.cycles_per_frame):
                chip.execute_cycle()
                if chip.halted:
                    break
            chip.decrement_timers()

            # Silent "audio": indicator only. Optional bell fires once on the
            # rising edge of ST, never once per frame.
            if chip.sound_timer > 0 and self._prev_sound == 0 and self.bell_var.get():
                try:
                    self.root.bell()
                except tk.TclError:
                    pass
            self._prev_sound = chip.sound_timer

            if chip.draw_flag:
                self._redraw_display()
                chip.draw_flag = False

            self.frame_count += 1
            now = time.perf_counter()
            elapsed = now - self.last_fps_update
            if elapsed >= 1.0:
                self.fps = self.frame_count / elapsed
                self.frame_count = 0
                self.last_fps_update = now
                self._update_status()

        # Drift-compensated ~60 Hz scheduling.
        self._next_frame += 1.0 / TARGET_FPS
        delay_s = self._next_frame - time.perf_counter()
        if delay_s < -0.25:                      # fell way behind: resync
            self._next_frame = time.perf_counter()
            delay_s = 0.0
        self._after_id = self.root.after(max(1, int(delay_s * 1000)), self._update_loop)

    def _on_close(self):
        if self._after_id is not None:
            try:
                self.root.after_cancel(self._after_id)
            except tk.TclError:
                pass
            self._after_id = None
        self.root.destroy()


# =============================================================================
# Entry Point
# =============================================================================
def main():
    root = tk.Tk()
    Chip8EmulatorGUI(root)
    root.mainloop()


if __name__ == "__main__":
    main()
