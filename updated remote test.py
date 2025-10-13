# -*- coding: utf-8 -*-
"""
Serial Remote Display Emulator (LaserLight3-style)

WHAT'S NEW (this build)
- Per-mode display caps (visible on-screen only; EDP command preserves full text):
    * DM1, DMQ:   8 chars visible per line/quadrant
    * DM2, DM4:   16 chars visible per line
    * DMT:        6 chars visible (single line)
  Scrolling shows the full message beyond the visible cap.
- DMT traffic selector uses labeled names and inserts numeric code 0–7:
    0 = Red Stop Light, 1 = Green Go light, 2 = Red X, 3 = Arrow Up,
    4 = Arrow Right,    5 = Arrow Down,     6 = Arrow Left, 7 = No Icon
- Traffic icon draws in the weight area even when not in legacy mode
  (small overlay in the top-left; does not block text).
- EDP console shows the full built command string (no truncation).

Existing features (abridged):
- DM1/DMT: single line; DM2: two lines; DM4: four lines; DMQ: 2x2 quadrants (no borders)
- Color field for all DMx = concatenated pairs (no separators) e.g. DM2 "WYWY"
- RLWS parsing; auto-learn; mirror; hold-last-weight; dark UI theme
"""
from __future__ import annotations

import time, threading, re, math
from dataclasses import dataclass
from typing import Optional, Dict, List, Tuple

try:
    import serial  # type: ignore
    import serial.tools.list_ports as list_ports  # type: ignore
except ImportError:
    serial = None  # type: ignore
    list_ports = None  # type: ignore

try:
    from serial import SerialException  # type: ignore
except ImportError:
    class SerialException(Exception):  # type: ignore
        pass

import tkinter as tk
from tkinter import ttk, messagebox
from tkinter.scrolledtext import ScrolledText
from tkinter import font as tkfont

# ---- Layout & font knobs ---------------------------------------------
RIGHT_COL_WIDTH   = 640   # px
LOG_BOX_HEIGHT    = 112   # px
EDP_BOX_HEIGHT    = 75    # px
EDITOR_HEIGHT     = 490   # px
GLOBAL_FONT_BUMP  = 4     # +N to Tk default/text/fixed fonts (weight box unaffected)

# ---- Control bytes ---------------------------------------------------
STX = 0x02
CR  = 0x0D
LF  = 0x0A

# ---- Traffic (DMT) mapping ------------------------------------------
TRAFFIC_LABELS: List[str] = [
    "0 = Red Stop Light",
    "1 = Green Go light",
    "2 = Red X",
    "3 = Arrow Up",
    "4 = Arrow Right",
    "5 = Arrow Down",
    "6 = Arrow Left",
    "7 = No Icon",
]
# map first digit in label to canonical internal state
TRAFFIC_CODE_TO_STATE: Dict[str, str] = {
    "0": "RED",
    "1": "GREEN",
    "2": "REDX",
    "3": "ARROWUP",
    "4": "ARROWRIGHT",
    "5": "ARROWDOWN",
    "6": "ARROWLEFT",
    "7": "OFF",
}

# Defaults per manual
DEFAULT_UNITDEF   = {'G': 'Gram', 'K': 'Kilogram', 'L': 'Pound', 'O': 'Ounce', 'T': 'Metric Ton', 't': 'Ton'}
DEFAULT_MODEDEF   = {'G': 'Gross', 'N': 'Net'}
DEFAULT_STATUSDEF = {' ': 'Valid', 'I': 'Invalid', 'M': 'In motion', 'O': 'Over/Under', 'Z': 'Center of Zero'}

# ---- RLWS parsed frame -----------------------------------------------
@dataclass
class ParsedRLWS:
    p: str  # polarity ' ' or '-'
    w: str  # width 7 (with optional '.')
    u: str  # unit letter
    m: str  # mode letter
    s: str  # status letter/space

# ---- Tokenized pattern helpers ---------------------------------------
TOKEN_RE = re.compile(r"<([^>]+)>")

def token_to_regex_bytes(token: str) -> re.Pattern:
    """Convert tokenized pattern (manual format) to regex."""
    def _tok(name: str) -> bytes:
        n = name.strip().upper()
        if n in ("2", "STX"):  return b"\x02"
        if n == 'CR':          return b"\x0D"
        if n == 'LF':          return b"\x0A"
        if n == 'ETX':         return b"\x03"
        if n == 'SP':          return b" "
        if n == 'SP2':         return b"  "
        if n == 'P':           return b"(?P<P>[- ])"
        if n == 'U':           return b"(?P<U>[A-Za-z])"
        if n == 'UU':          return b"(?P<U>[A-Za-z]{2})"
        if n == 'M':           return b"(?P<M>[A-Za-z])"
        if n == 'S' or n.startswith('S'):
                                return b"(?P<S>.)"
        if n.startswith('W'):
            m = re.match(r"W(-?)(\d+)(\.*)", n)
            if m:
                width = int(m.group(2))
                return f"(?P<W>.{{{width}}})".encode('ascii')
        if len(n) == 1:
            return re.escape(n).encode('ascii')
        return b''
    out: List[bytes] = []
    i = 0
    for m in TOKEN_RE.finditer(token):
        lit = token[i:m.start()].encode('ascii', 'ignore')
        if lit:
            out.append(re.escape(lit))
        out.append(_tok(m.group(1)))
        i = m.end()
    lit = token[i:].encode('ascii', 'ignore')
    if lit:
        out.append(re.escape(lit))
    return re.compile(b''.join(out), re.DOTALL)

KNOWN_FORMATS: Dict[str, str] = {
    'RLWS (Condec) – W7': '<STX><P><W7.><U><M><S><CR><LF>',
    'Cardinal – W7': '<CR><P><W7.><S><SP><U><SP><M><SP2><ETX>',
    'Dini Argeo – CSV W7 UU': '<SS>,<MM>,<P><W7.>,<UU><CR><LF>',
    'Fairbanks – STX…ETX (W-7)': '<STX><SS><W-7.><ETX>',
    'GSE Scale Systems – words': '<STX><W8><SP><UNIT><SP><MODE><CR><LF>',
    'Hardy – 65-char (gross only)': '<CR><LF><SP>GROSS<SP><-W7.><SP><UU><SP><CR><LF>',
    'Weightronix – W6': '<TR><M><P><W6.><SP><U><CR><LF>',
}
KNOWN_PATTERNS: Dict[str, re.Pattern] = {name: token_to_regex_bytes(tok) for name, tok in KNOWN_FORMATS.items()}

# ---- RLWS frame reader -----------------------------------------------
class RLWSReader:
    """State machine for RLWS framed messages (STX ... CR)."""
    def __init__(self, on_frame):
        self.on_frame = on_frame
        self._buf = bytearray()
        self._in = False

    def feed(self, data: bytes) -> None:
        for b in data:
            if not self._in:
                if b == STX:
                    self._in = True
                    self._buf.clear()
                continue
            if b == CR:
                payload = bytes(self._buf)
                self._in = False
                self._buf.clear()
                self.on_frame(payload)
            else:
                self._buf.append(b)

# ---- Serial thread (I/O + learn) -------------------------------------
class SerialThread(threading.Thread):
    """Background thread handling serial I/O and auto-learn logic."""
    def __init__(self, app: 'App') -> None:
        super().__init__(daemon=True)
        self.app = app
        self.stop_evt = threading.Event()
        self.rlws = RLWSReader(self.on_rlws_payload)
        self.line_buf = bytearray()
        self.auto_learn = False
        self.learn_hits: Dict[str, int] = {}
        self.learn_lock = threading.Lock()

    def stop(self) -> None:
        self.stop_evt.set()

    def set_auto_learn(self, enabled: bool) -> None:
        with self.learn_lock:
            self.auto_learn = enabled
            self.learn_hits.clear()

    def run(self) -> None:
        while not self.stop_evt.is_set():
            ser = self.app.ser
            if ser is None or not ser.is_open:
                time.sleep(0.05)
                continue
            try:
                data = ser.read(256)
                if not data:
                    continue
                # RLWS framed payloads
                self.rlws.feed(data)
                # EDP lines (textual)
                for b in data:
                    if b in (CR, LF, 0x21):  # '!'
                        if b == 0x21:
                            self.line_buf.append(b)
                        if self.line_buf:
                            line = bytes(self.line_buf).decode('ascii', 'ignore').strip()
                            self.line_buf.clear()
                            if line:
                                self.app.on_edp_line(line)
                    else:
                        if b >= 0x20:
                            self.line_buf.append(b)
                # Learn known formats
                if self.auto_learn:
                    self._auto_learn_scan(data)
            except (SerialException, OSError) as e:
                self.app.log(f"Serial error: {e}")
                time.sleep(0.2)

    def _auto_learn_scan(self, data: bytes) -> None:
        self.app.learn_buf.extend(data)
        if len(self.app.learn_buf) > 4096:
            del self.app.learn_buf[:2048]
        buf = bytes(self.app.learn_buf)
        with self.learn_lock:
            for name, pat in KNOWN_PATTERNS.items():
                for _ in pat.finditer(buf):
                    self.learn_hits[name] = self.learn_hits.get(name, 0) + 1
            if self.learn_hits:
                best = max(self.learn_hits.items(), key=lambda kv: kv[1])
                if best[1] >= 3:
                    self.auto_learn = False
                    try:
                        self.app.on_auto_learn_success(best[0])
                    except Exception:
                        pass
                    self.learn_hits.clear()

    def on_rlws_payload(self, payload: bytes) -> None:
        self.app.on_rlws_payload(payload)

# ---- EDP interpreter --------------------------------------------------
class EDP:
    """Simple interpreter for EDP commands."""
    def __init__(self, app: 'App') -> None:
        self.app = app
        self.vars: Dict[str, str] = {
            'BRIGHT.INTENSITY': '6',
            'DISPLAY.COLOR': 'Red',
            'DISPLAY.BGCOLOR': 'NONE',
            'DISPLAY.TYPE': 'Standard',
            'MSGTIME': '5',
            'TIMEDATE': 'OFF',
            'MIRROR': 'OFF',
            'ADDRESS': '0',
            'LEARN.HOLDWT': 'OFF',
        }
        self.unitdef = DEFAULT_UNITDEF.copy()
        self.modedef = DEFAULT_MODEDEF.copy()
        self.statusdef = DEFAULT_STATUSDEF.copy()

    def handle(self, line: str) -> str:
        s = line.strip()

        # Back-compat: inline DO form like |AADOx!| or "DO=3"
        if s.endswith('!') and 'DO' in s:
            core = s
            if core.startswith('|'):
                core = core[1:]
            if core.endswith('!'):
                core = core[:-1]
            if len(core) >= 5 and core[:2].isdigit() and core[2:4].upper() == 'DO':
                nib = core[4]
                return self.app.handle_do(nib)

        if s.upper().startswith('DO'):
            tail = s[2:].strip()
            if tail.startswith('='):
                tail = tail[1:].strip()
            if tail:
                return self.app.handle_do(tail[0])

        if s.upper() == 'VERSION':
            return 'EMULATOR v17c\r\n'
        if s.upper() == 'BUILD':
            return 'EMULATOR v17c build 1\r\n'
        if s.upper() == 'REMOTE.FORMAT':
            return f"{self.app.remote_format}\r\n"
        if s.upper() == 'DUMPALL':
            items = [f"{k}={v}" for k, v in sorted(self.vars.items())]
            return ("\r\n".join(items) + "\r\n")
        if s.upper().startswith('K'):
            return 'OK\r\n'

        # key=value
        m = re.match(r"^([A-Za-z0-9_.]+)\s*=\s*(.+)$", s)
        if m:
            key = m.group(1).upper()
            val = m.group(2).strip()
            if val.upper() in ('ON', 'OFF'):
                val = val.upper()

            if key in self.vars:
                self.vars[key] = val
                if key == 'DISPLAY.COLOR':
                    self.app.set_display_color(val)
                elif key == 'BRIGHT.INTENSITY':
                    self.app.set_brightness(val)
                elif key == 'DISPLAY.TYPE':
                    self.app.set_display_type(val)
                elif key == 'DISPLAY.BGCOLOR':
                    self.app.set_background_color(val)
                elif key == 'MIRROR':
                    self.app.set_mirror(val == 'ON')
                elif key == 'LEARN.HOLDWT':
                    self.app.set_hold_weight(val == 'ON')
                elif key == 'ADDRESS':
                    self.app.address = val
                return 'OK\r\n'

            if key.startswith('UNITDEF.'):
                tag = key.split('.', 1)[1]
                self.unitdef[tag[:2]] = val
                return 'OK\r\n'
            if key.startswith('MODEDEF.'):
                tag = key.split('.', 1)[1]
                self.modedef[tag.upper()] = val
                return 'OK\r\n'
            if key.startswith('STATUSDEF.'):
                tag = key.split('.', 1)[1]
                self.statusdef[tag.upper()] = val
                return 'OK\r\n'

            return '?? invalid command\r\n'

        if s.upper() in self.vars:
            return f"{self.vars[s.upper()]}\r\n"

        return '?? invalid command\r\n'

# ------------------------------ SECTION 2/4 ------------------------------
# Tk App (UI: top bar, display area, right panel, Builder with DMT labels→code)

class App:
    """Tkinter GUI emulating a serial remote display."""
    # ---- visible caps are DISPLAY-ONLY; EDP preserves full strings ----
    def _char_cap_for_display(self, cmd: str) -> int:
        # What the DISPLAY can show at once. Scrolling (handled in renderer)
        # will reveal the rest; the EDP command itself is NOT truncated.
        if cmd == 'DMT': return 6
        if cmd in ('DM1', 'DMQ'): return 8
        if cmd in ('DM2', 'DM4'): return 16
        return 8

    def __init__(self, root: tk.Tk) -> None:
        self.root = root
        root.title('Serial Remote Display Emulator v17c')
        root.geometry('1280x860')
        root.minsize(1100, 760)
        self.style = ttk.Style(root)

        # ---- state pre-init ----
        self.current_bg_hex = '#000000'
        self.mirror = False
        self.hold_weight = False
        self.last_good_weight: Optional[str] = None
        self.remote_format = 'RLWS'
        self.address = '0'
        self.learn_buf = bytearray()

        # serial & worker thread placeholders (created/started later)
        self.ser: Optional[serial.Serial] = None  # type: ignore
        self.reader: Optional[SerialThread] = None

        # message timing (DM timeout)
        self.message_end_time = 0.0
        self.message_timeout = 5.0

        # animation state placeholders (filled in renderer section)
        self._flash_flags: List[str] = []
        self._slide_flags: List[str] = []
        self._scroll_flags: List[str] = []
        self.flash_state = False
        self.flash_timer = None
        self.slide_position: Dict[int, int] = {}
        self.slide_timer = None
        self.scroll_position: Dict[int, int] = {}
        self.scroll_timer = None

        # display mode and last DM payload for redraw
        self.display_mode = 'weight'
        self._last_dm: Optional[Tuple[str, List[str], str]] = None  # (cmd, lines(full), color_field)

        # footer & theme
        self.footer = ttk.Label(root, text='Idle', anchor='w')
        self.footer.pack(fill=tk.X, padx=12, pady=6)
        self._status_messages: List[str] = []
        self._log_buffer: List[str] = []
        self._set_dark_theme()

        # ---- Top bar --------------------------------------------------
        top = ttk.Frame(root, padding=10)
        top.pack(side=tk.TOP, fill=tk.X)

        self.port_var = tk.StringVar()
        self.baud_var = tk.StringVar(value='9600')
        self.bytesize_var = tk.StringVar(value='8')
        self.parity_var = tk.StringVar(value='N')
        self.stopbits_var = tk.StringVar(value='1')

        ttk.Label(top, text='Port').grid(row=0, column=0, sticky='w')
        self.port_cb = ttk.Combobox(top, textvariable=self.port_var, width=16, state='readonly', style='Big.TCombobox')
        self.port_cb['values'] = self._list_ports()
        self.port_cb.grid(row=1, column=0, sticky='we', padx=(0, 8))
        ttk.Button(top, text='↻', width=3, command=self.refresh_ports).grid(row=1, column=1, sticky='w')

        ttk.Label(top, text='Baud').grid(row=0, column=2, sticky='w')
        self.baud_cb = ttk.Combobox(top, textvariable=self.baud_var, width=10,
                                    values=['1200','2400','4800','9600','19200','38400','57600','115200'],
                                    style='Big.TCombobox')
        self.baud_cb.grid(row=1, column=2, sticky='we', padx=(16, 8))

        ttk.Label(top, text='Data').grid(row=0, column=3, sticky='w')
        self.bytesize_cb = ttk.Combobox(top, textvariable=self.bytesize_var, width=5, values=['7','8'],
                                        style='Big.TCombobox')
        self.bytesize_cb.grid(row=1, column=3, sticky='we', padx=(8, 8))

        ttk.Label(top, text='Parity').grid(row=0, column=4, sticky='w')
        self.parity_cb = ttk.Combobox(top, textvariable=self.parity_var, width=5, values=['N','E','O'],
                                      style='Big.TCombobox')
        self.parity_cb.grid(row=1, column=4, sticky='we', padx=(8, 8))

        ttk.Label(top, text='Stop').grid(row=0, column=5, sticky='w')
        self.stopbits_cb = ttk.Combobox(top, textvariable=self.stopbits_var, width=5, values=['1','2'],
                                        style='Big.TCombobox')
        self.stopbits_cb.grid(row=1, column=5, sticky='we', padx=(8, 8))

        self.btn_open = ttk.Button(top, text='Open', command=self.toggle_port)
        self.btn_open.grid(row=1, column=6, padx=(16, 8))

        self.autolearn_var = tk.BooleanVar(value=False)
        self.holdwt_var = tk.BooleanVar(value=False)
        ttk.Checkbutton(top, text='Auto-Learn', variable=self.autolearn_var,
                        command=self.on_autolearn_toggle).grid(row=1, column=7, padx=(16, 4))
        ttk.Checkbutton(top, text='Hold Last Weight', variable=self.holdwt_var,
                        command=self.on_hold_toggle).grid(row=1, column=8, padx=(4, 0))

        ttk.Label(top, text='Type').grid(row=0, column=9, sticky='w')
        self.type_var = tk.StringVar(value='Standard')
        self.type_cb = ttk.Combobox(top, textvariable=self.type_var, width=12,
                                    values=['Standard', 'Legacy', 'Cardnal'],
                                    state='readonly', style='Big.TCombobox')
        self.type_cb.grid(row=1, column=9, sticky='we', padx=(16, 8))
        self.type_cb.bind('<<ComboboxSelected>>', lambda e: self.set_display_type(self.type_var.get()))

        ttk.Label(top, text='Color').grid(row=0, column=10, sticky='w')
        self.color_var = tk.StringVar(value='Red')
        self.color_cb = ttk.Combobox(top, textvariable=self.color_var, width=12,
                                     values=['Red','Yellow','Green','Blue','Magenta','Cyan','White'],
                                     state='readonly', style='Big.TCombobox')
        self.color_cb.grid(row=1, column=10, sticky='we', padx=(8, 8))
        self.color_cb.bind('<<ComboboxSelected>>', lambda e: self.set_display_color(self.color_var.get()))

        ttk.Label(top, text='BG').grid(row=0, column=11, sticky='w')
        self.bg_color_var = tk.StringVar(value='NONE')
        self.bg_color_cb = ttk.Combobox(top, textvariable=self.bg_color_var, width=12,
                                        values=['NONE','Red','Yellow','Green','Blue','Magenta','Cyan','White'],
                                        state='readonly', style='Big.TCombobox')
        self.bg_color_cb.grid(row=1, column=11, sticky='we', padx=(8, 8))
        self.bg_color_cb.bind('<<ComboboxSelected>>', lambda e: self.set_background_color(self.bg_color_var.get()))

        # Legacy mode: DO shortcut dropdown (updates stop sign indicator and fills EDP console)
        ttk.Label(top, text='Legacy DO').grid(row=0, column=12, sticky='w', padx=(16, 0))
        self.legacy_do_var = tk.StringVar(value='Off')
        self.legacy_do_cb = ttk.Combobox(
            top,
            textvariable=self.legacy_do_var,
            width=16,
            values=['Off', 'Green Arrow', 'Green Circle', 'Stop'],
            state='disabled',
            style='Big.TCombobox'
        )
        self.legacy_do_cb.grid(row=1, column=12, sticky='we', padx=(8, 0))
        self.legacy_do_cb.bind('<<ComboboxSelected>>', lambda e: self.on_legacy_do_selected())

        # Minimize button for a cleaner desktop
        self.btn_minimize = ttk.Button(top, text='Minimize', width=10, command=self.minimize_window)
        self.btn_minimize.grid(row=1, column=13, padx=(12, 0))

        # ---- Center (left display + right panel) ----------------------
        center = ttk.Frame(root, padding=12)
        center.pack(side=tk.TOP, fill=tk.BOTH, expand=True)

        content = ttk.Frame(center)
        content.pack(side=tk.TOP, fill=tk.BOTH, expand=True)

        # LEFT column: weight/DM display
        left = ttk.Frame(content)
        left.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

        self.display_area = ttk.Frame(left)
        self.display_area.pack(fill=tk.X, expand=False, pady=(0, 2))
        self.display_area.configure(height=200)
        self.display_area.pack_propagate(False)

        # main weight label
        self.weight_font = tkfont.Font(family='Segoe UI', size=82, weight='bold')
        self.style.configure('Weight.TLabel', padding=0, background='#000000')
        self.weight_label = ttk.Label(self.display_area, text='NO DATA', font=self.weight_font,
                                      anchor='e', justify='right', style='Weight.TLabel')
        self.weight_label.pack(fill=tk.BOTH, expand=True)

        # DM canvas (for DM1/2/4/Q/T text rendering)
        self.dm_canvas = tk.Canvas(self.display_area, highlightthickness=0, bd=0, relief='flat')

        # Small always-available traffic/icon overlay (top-left), hidden by default
        # (Shown when DMT provides a code OR legacy mode requests it.)
        self.icon_canvas = tk.Canvas(self.display_area, width=44, height=44,
                                     highlightthickness=0, bd=0, relief='flat', bg=self.current_bg_hex)
        self.icon_canvas.place(x=6, y=6)
        self.icon_canvas.place_forget()  # hidden until needed
        self.icon_state = 'OFF'          # one of RED, GREEN, REDX, ARROWUP/RIGHT/DOWN/LEFT, OFF

        # units/mode row
        row2 = ttk.Frame(left)
        row2.pack(fill=tk.X)
        self.units_label = ttk.Label(row2, text='', width=10, anchor='w', font=('Segoe UI', 24))
        self.units_label.pack(side=tk.LEFT)
        self.mode_label = ttk.Label(row2, text='', width=14, anchor='w', font=('Segoe UI', 20))
        self.mode_label.pack(side=tk.LEFT, padx=(16, 0))

        # track labels for theme changes
        self.units_label.configure(foreground='red')
        self.mode_label.configure(foreground='red')
        self._display_labels = [self.weight_label, self.units_label, self.mode_label]

        # RIGHT column: log + EDP console + builder
        right = ttk.Frame(content)
        right.pack(side=tk.RIGHT, fill=tk.Y, padx=(8, 0))
        right.configure(width=RIGHT_COL_WIDTH)
        right.pack_propagate(False)

        # Frames Log
        log_box = ttk.LabelFrame(right, text='Frames Log', padding=6)
        log_box.pack(fill=tk.X)
        log_box.configure(height=LOG_BOX_HEIGHT)
        log_box.pack_propagate(False)
        self.log_view = ScrolledText(log_box, wrap='none')
        self.log_view.pack(fill=tk.BOTH, expand=True)
        self.log_view.configure(background='#111418', foreground='#E6EDF3', insertbackground='#E6EDF3')
        if self._log_buffer:
            for msg in self._log_buffer:
                self.log_view.insert(tk.END, msg)
            self.log_view.see(tk.END)
            self._log_buffer.clear()

        # EDP console (shows FULL command string, no truncation)
        edp_box = ttk.LabelFrame(right, text='EDP Console', padding=8)
        edp_box.pack(fill=tk.X, pady=(8, 0))
        edp_box.configure(height=EDP_BOX_HEIGHT)
        edp_box.pack_propagate(False)
        self.edp_entry = ttk.Entry(edp_box)
        self.edp_entry.pack(side=tk.LEFT, fill=tk.X, expand=True)
        ttk.Button(edp_box, text='Send', command=self.send_edp).pack(side=tk.LEFT, padx=(8, 0))

        # Bottom: Builder
        editor_container = ttk.Frame(center)
        editor_container.pack(side=tk.BOTTOM, fill=tk.X, pady=(10, 0))
        editor_container.configure(height=EDITOR_HEIGHT)
        editor_container.pack_propagate(False)

        self.builder_box = ttk.LabelFrame(editor_container, text='Advanced Display Message (DM) – Builder', padding=10)
        self.builder_box.pack(fill=tk.BOTH, expand=True)
        self._init_command_builder(self.builder_box)

        # initial BG & color
        try:
            self.set_background_color('NONE')
        except tk.TclError:
            pass

        # re-render DM on resize (hooked later when renderer is in place)
        self.dm_canvas.bind('<Configure>', lambda e: getattr(self, '_redraw_dm', lambda: None)())

    # ---- UI helpers & theme ------------------------------------------
    def _set_dark_theme(self) -> None:
        self.style.theme_use('clam')
        bg = '#0D1117'
        fg = '#E6EDF3'
        acc = '#30363D'
        self.root.configure(bg=bg)
        self.style.configure('.', background=bg, foreground=fg, fieldbackground='#161B22')
        self.style.configure('TLabel', background=bg, foreground=fg)
        self.style.configure('TFrame', background=bg)
        self.style.configure('TButton', background=acc, foreground=fg, padding=(10, 4))
        self.style.configure('TLabelframe', background=bg, foreground=fg)
        self.style.configure('TLabelframe.Label', background=bg, foreground=fg)
        self.style.configure('Weight.TLabel', background='#000000', padding=0)

        try:
            default = tkfont.nametofont("TkDefaultFont")
            text = tkfont.nametofont("TkTextFont")
            fixed = tkfont.nametofont("TkFixedFont")
            for f in (default, text, fixed):
                f.configure(size=f.cget("size") + GLOBAL_FONT_BUMP)
        except tk.TclError:
            pass

        self.style.configure('Big.TCombobox',
                             fieldbackground='#1b2330',
                             foreground='#E6EDF3',
                             arrowcolor='#E6EDF3',
                             padding=4,
                             font=('Segoe UI', max(12, 12 + GLOBAL_FONT_BUMP - 2)))
        self.style.map('Big.TCombobox',
                       fieldbackground=[('readonly', '#1b2330')],
                       foreground=[('readonly', '#E6EDF3')])

    def set_status(self, message: str) -> None:
        try:
            self.footer.configure(text=message)
        except tk.TclError:
            pass

    def minimize_window(self) -> None:
        try:
            self.root.iconify()
        except Exception:
            pass

    def log(self, msg: str) -> None:
        ts = time.strftime('%H:%M:%S')
        formatted = f'[{ts}] {msg}\n'
        try:
            self.log_view.insert(tk.END, formatted)
            self.log_view.see(tk.END)
        except Exception:
            self._log_buffer.append(formatted)

    # ---- Ports & serial controls (basic) ------------------------------
    def _list_ports(self) -> List[str]:
        if list_ports is None:
            self.log('Error: pyserial module not installed')
            self.set_status('Error: pyserial module not installed')
            return []
        try:
            ports = []
            for p in list_ports.comports():
                desc = f"{p.device}"
                if p.description and p.description != "n/a":
                    desc += f" ({p.description})"
                ports.append(desc)
            if not ports:
                self.log('No serial ports detected - connect a device and refresh')
                self.set_status('No serial ports detected')
            else:
                self.log(f'Found {len(ports)} serial port(s)')
                for p in ports:
                    self.log(f'  {p}')
                self.set_status(f'Found {len(ports)} serial port(s)')
            return ports
        except Exception as e:
            self.log(f'Error listing ports: {e}')
            self.set_status('Error listing ports')
            return []

    def refresh_ports(self) -> None:
        try:
            current = self.port_var.get().split(' (')[0] if self.port_var.get() else ''
            ports = self._list_ports()
            if ports:
                self.port_cb['values'] = ports
                self.port_cb.configure(state='readonly')
                if current and any(p.startswith(current) for p in ports):
                    for p in ports:
                        if p.startswith(current):
                            self.port_var.set(p)
                            break
                else:
                    self.port_var.set('')
            else:
                self.port_cb['values'] = ['No ports available']
                self.port_cb.configure(state='disabled')
                self.port_var.set('')
        except Exception as e:
            self.log(f'Error refreshing ports: {e}')
            self.port_cb['values'] = ['Error listing ports']
            self.port_cb.configure(state='disabled')
            self.port_var.set('')

    def toggle_port(self) -> None:
        if self.ser and getattr(self.ser, 'is_open', False):
            self.close_port()
        else:
            self.open_port()

    def open_port(self) -> None:
        if serial is None:
            self.log('pyserial not installed (pip install pyserial)')
            try:
                messagebox.showerror('Module Missing', 'Install pyserial: pip install pyserial')
            except Exception:
                pass
            self.set_status('Error: pyserial missing')
            return

        port = self.port_var.get().split(' (')[0] if self.port_var.get() else ''
        if not port or port in ('No ports available', 'Error listing ports'):
            self.log('No valid port selected')
            try:
                messagebox.showwarning('Port Required', 'Select a valid serial port and try again.')
            except Exception:
                pass
            return

        try:
            baud = int(self.baud_var.get())
            bytesize = serial.SEVENBITS if self.bytesize_var.get() == '7' else serial.EIGHTBITS
            parity_map = {'N': serial.PARITY_NONE, 'E': serial.PARITY_EVEN, 'O': serial.PARITY_ODD}
            parity = parity_map[self.parity_var.get()]
            stopbits = serial.STOPBITS_TWO if self.stopbits_var.get() == '2' else serial.STOPBITS_ONE

            available = [p.device for p in list_ports.comports()] if list_ports else []
            if port not in available:
                self.log(f'Port {port} no longer available')
                try:
                    messagebox.showerror('Port Not Found', f'Port {port} not found. Refresh and select again.')
                except Exception:
                    pass
                self.set_status('Error: Port not found')
                self.refresh_ports()
                return

            self.ser = serial.Serial(port=port, baudrate=baud, bytesize=bytesize,
                                     parity=parity, stopbits=stopbits,
                                     timeout=0.2, write_timeout=1.0)
            self.btn_open.configure(text='Close')
            settings = f'{baud} {self.bytesize_var.get()}{self.parity_var.get()}{self.stopbits_var.get()}'
            self.set_status(f'Connected to {port} @ {settings}')
            self.log(f'Successfully opened {port} @ {settings}')

            # start reader thread if not running yet
            if self.reader is None:
                self.reader = SerialThread(self)
                self.reader.start()
            # propagate autolearn state
            self.reader.set_auto_learn(self.autolearn_var.get())

        except (SerialException, OSError) as e:
            self.log(f'Failed to open {port}: {e}')
            try:
                messagebox.showerror('Connection Failed', str(e))
            except Exception:
                pass
            self.set_status('Error: Connection failed')
        except ValueError as e:
            self.log(f'Invalid serial settings: {e}')
            try:
                messagebox.showerror('Invalid Settings', str(e))
            except Exception:
                pass
            self.set_status('Error: Invalid settings')

    def close_port(self) -> None:
        try:
            if self.ser:
                self.ser.close()
                self.log('Port closed')
                self.set_status('Closed normally')
        except Exception as e:
            self.log(f'Error closing port: {e}')
            self.set_status('Close error')
        finally:
            self.ser = None
            self.btn_open.configure(text='Open')

    # ---- Top bar toggles ---------------------------------------------
    def on_autolearn_toggle(self) -> None:
        if self.reader:
            self.reader.set_auto_learn(self.autolearn_var.get())
        self.log(f'Auto-Learn {"ON" if self.autolearn_var.get() else "OFF"}')

    def on_auto_learn_success(self, name: str) -> None:
        try:
            self.remote_format = name
        except Exception:
            pass
        self.log(f'Auto-Learn detected format: {name}')
        self.set_status(f'Auto-Learn: {name}')

    def on_hold_toggle(self) -> None:
        self.set_hold_weight(self.holdwt_var.get())

    # ---- Legacy DO dropdown handler ----------------------------------
    def on_legacy_do_selected(self) -> None:
        label = (self.legacy_do_var.get() or '').strip()
        # Map label to DO nibble per requested mapping
        label_to_nib = {
            'Off': '0',
            'Green Arrow': '1',
            'Green Circle': '2',
            'Stop': '3',
        }
        nib = label_to_nib.get(label, '0')
        cmd = f"|00DO{nib}!"
        # Populate EDP console with full command
        self._fill_edp_prompt(cmd)
        # Apply immediately so the indicator updates in Legacy mode
        try:
            self.on_edp_line(cmd)
        except Exception:
            pass

    # ---- EDP console actions -----------------------------------------
    def send_edp(self) -> None:
        s = self.edp_entry.get().strip()
        if not s:
            return
        # Full string is passed; no truncation here.
        try:
            self.on_edp_line(s)  # defined in Section 3
        finally:
            self.edp_entry.delete(0, tk.END)

    def _fill_edp_prompt(self, s: str) -> None:
        # Show FULL command in console; do not truncate.
        try:
            self.edp_entry.delete(0, tk.END)
            self.edp_entry.insert(0, s)
            self.edp_entry.icursor(tk.END)
        except tk.TclError:
            pass

    # ---- Builder (DM1/2/4/Q/T) ---------------------------------------
    def _init_command_builder(self, parent: ttk.Frame) -> None:
        top = ttk.Frame(parent)
        top.pack(fill=tk.X)

        ttk.Label(top, text='Command').grid(row=0, column=0, sticky='w')
        self.dm_cmd_var = tk.StringVar(value='DM1')
        self.dm_cmd_cb = ttk.Combobox(top, textvariable=self.dm_cmd_var,
                                      values=['DM1', 'DM2', 'DM4', 'DMQ', 'DMT'],
                                      state='readonly', width=8, style='Big.TCombobox')
        self.dm_cmd_cb.grid(row=1, column=0, sticky='w')

        ttk.Label(top, text='Addr').grid(row=0, column=1, sticky='w', padx=(8, 0))
        self.dm_addr_var = tk.StringVar(value='00')
        ttk.Entry(top, textvariable=self.dm_addr_var, width=6).grid(row=1, column=1, sticky='w', padx=(8, 0))

        ttk.Label(top, text='Timeout (ms)').grid(row=0, column=2, sticky='w', padx=(8, 0))
        self.dm_timeout_var = tk.StringVar(value='0')
        ttk.Entry(top, textvariable=self.dm_timeout_var, width=8).grid(row=1, column=2, sticky='w', padx=(8, 0))

        ttk.Label(top, text='Scroll Count').grid(row=0, column=3, sticky='w', padx=(8, 0))
        self.dm_scrollcnt_var = tk.StringVar(value='0')
        ttk.Entry(top, textvariable=self.dm_scrollcnt_var, width=6).grid(row=1, column=3, sticky='w', padx=(8, 0))

        # two columns beneath (left/right)
        cols = ttk.Frame(parent)
        cols.pack(fill=tk.BOTH, expand=True, pady=(4, 0))
        self.dm_left_fr = ttk.Frame(cols)
        self.dm_left_fr.pack(side=tk.LEFT, fill=tk.BOTH, expand=True, padx=(0, 8))
        self.dm_right_fr = ttk.Frame(cols)
        self.dm_right_fr.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True)

        # dynamic containers
        self.dm_flags_fr = None
        self.dm_colors_fr = None
        self.dm_extra_fr = None
        self.dm_data_fr = None
        self.dm_hint_lbl = None
        self.dm_btns_fr = None

        # state holders
        self.dm_flash_vars: List[tk.StringVar] = []
        self.dm_slide_vars: List[tk.StringVar] = []
        self.dm_scroll_vars: List[tk.StringVar] = []
        self.dm_fc_vars: List[tk.StringVar] = []
        self.dm_bc_vars: List[tk.StringVar] = []
        self.dm_data_vars: List[tk.StringVar] = []

        self.dm_cmd_var.trace_add('write', lambda *_: self._rebuild_dm_sections())
        self._rebuild_dm_sections()

    def _rebuild_dm_sections(self) -> None:
        for fr in (self.dm_flags_fr, self.dm_colors_fr, self.dm_extra_fr,
                   self.dm_data_fr, self.dm_btns_fr, self.dm_hint_lbl):
            try:
                fr.destroy()
            except Exception:
                pass

        cmd = self.dm_cmd_var.get()
        nlines = 1 if cmd in ('DM1', 'DMT') else (2 if cmd == 'DM2' else 4)

        # Flags per line
        self.dm_flags_fr = ttk.LabelFrame(self.dm_left_fr, text='Flags per line', padding=8)
        self.dm_flags_fr.pack(fill=tk.X, pady=(8, 4))

        ttk.Label(self.dm_flags_fr, text='').grid(row=0, column=0, padx=(0, 6))
        ttk.Label(self.dm_flags_fr, text='Flash').grid(row=0, column=1, padx=(0, 12), sticky='w')
        ttk.Label(self.dm_flags_fr, text='Slide').grid(row=0, column=2, padx=(0, 12), sticky='w')
        ttk.Label(self.dm_flags_fr, text='Scroll').grid(row=0, column=3, padx=(0, 12), sticky='w')

        self.dm_flash_vars, self.dm_slide_vars, self.dm_scroll_vars = [], [], []
        for i in range(nlines):
            ttk.Label(self.dm_flags_fr, text=f'L{i+1}').grid(row=i+1, column=0, sticky='w', padx=(0, 6))
            fv = tk.StringVar(value='N')
            sv = tk.StringVar(value='N')
            rv = tk.StringVar(value='N')
            ttk.Combobox(self.dm_flags_fr, textvariable=fv, values=['Y','N'], width=4,
                         state='readonly', style='Big.TCombobox').grid(row=i+1, column=1, sticky='w', padx=(0, 12))
            ttk.Combobox(self.dm_flags_fr, textvariable=sv, values=['Y','N'], width=4,
                         state='readonly', style='Big.TCombobox').grid(row=i+1, column=2, sticky='w', padx=(0, 12))
            ttk.Combobox(self.dm_flags_fr, textvariable=rv, values=['Y','N'], width=4,
                         state='readonly', style='Big.TCombobox').grid(row=i+1, column=3, sticky='w', padx=(0, 12))
            self.dm_flash_vars.append(fv); self.dm_slide_vars.append(sv); self.dm_scroll_vars.append(rv)

        # Colors per line (Text / Background)
        self.dm_colors_fr = ttk.LabelFrame(self.dm_left_fr, text='Colors per line (Text / Background)', padding=8)
        self.dm_colors_fr.pack(fill=tk.X, pady=(4, 4))
        color_opts = ['Space', 'R', 'Y', 'G', 'B', 'M', 'C', 'W']
        self.dm_fc_vars, self.dm_bc_vars = [], []
        for i in range(nlines):
            ttk.Label(self.dm_colors_fr, text=f'L{i+1}').grid(row=i, column=0, sticky='w', padx=(0, 6))
            ttk.Label(self.dm_colors_fr, text='Text').grid(row=i, column=1, sticky='w')
            fcv = tk.StringVar(value='W')
            ttk.Combobox(self.dm_colors_fr, textvariable=fcv, values=color_opts, width=8,
                         state='readonly', style='Big.TCombobox').grid(row=i, column=2, sticky='w', padx=(0, 12))
            ttk.Label(self.dm_colors_fr, text='Background').grid(row=i, column=3, sticky='w')
            bcv = tk.StringVar(value='Space')
            ttk.Combobox(self.dm_colors_fr, textvariable=bcv, values=color_opts, width=8,
                         state='readonly', style='Big.TCombobox').grid(row=i, column=4, sticky='w', padx=(0, 12))
            self.dm_fc_vars.append(fcv); self.dm_bc_vars.append(bcv)

        # Extras (right)
        self.dm_extra_fr = ttk.LabelFrame(self.dm_right_fr, text='Extras', padding=8)
        self.dm_extra_fr.pack(fill=tk.X, pady=(4, 4))

        self.dm_include_ann_var = tk.BooleanVar(value=False)
        include_ann = ttk.Checkbutton(self.dm_extra_fr, text='Include Mode/Units (DM1/DMT)',
                                      variable=self.dm_include_ann_var)
        include_ann.grid(row=0, column=0, sticky='w')

        ttk.Label(self.dm_extra_fr, text='Mode (G/N)').grid(row=0, column=1, sticky='w', padx=(8, 0))
        self.dm_mode_var = tk.StringVar(value='G')
        ttk.Combobox(self.dm_extra_fr, textvariable=self.dm_mode_var, values=['G','N'], width=4,
                     state='readonly', style='Big.TCombobox').grid(row=0, column=2, sticky='w')

        ttk.Label(self.dm_extra_fr, text='Units').grid(row=0, column=3, sticky='w', padx=(8, 0))
        self.dm_units_var = tk.StringVar(value='lb')
        ttk.Combobox(self.dm_extra_fr, textvariable=self.dm_units_var,
                     values=['lb','kg','t','tn','oz','gr'], width=6,
                     state='readonly', style='Big.TCombobox').grid(row=0, column=4, sticky='w', padx=(0, 6))

        # DMT traffic (names with numbers; insert numeric field in command)
        ttk.Label(self.dm_extra_fr, text='Traffic Light (DMT ONLY)').grid(row=0, column=5, sticky='w', padx=(8, 0))
        self.dm_traffic_var = tk.StringVar(value='7 = No Icon')
        ttk.Combobox(self.dm_extra_fr, textvariable=self.dm_traffic_var, values=TRAFFIC_LABELS, width=22,
                     state='readonly', style='Big.TCombobox').grid(row=0, column=6, sticky='w')

        # Hide extras that don't apply
        if self.dm_cmd_var.get() not in ('DM1', 'DMT'):
            include_ann.state(['disabled'])
        if self.dm_cmd_var.get() != 'DMT':
            # hide traffic widgets if not DMT
            for child in self.dm_extra_fr.grid_slaves(row=0, column=5):
                child.grid_remove()
            for child in self.dm_extra_fr.grid_slaves(row=0, column=6):
                child.grid_remove()

        # Data entries
        self.dm_data_fr = ttk.LabelFrame(self.dm_right_fr, text='Data', padding=8)
        self.dm_data_fr.pack(fill=tk.BOTH, pady=(8, 6))
        self.dm_data_vars = []
        for i in range(nlines):
            var = tk.StringVar(value=('MESSAGE LINE 1' if i == 0 else f'LINE {i+1}'))
            ttk.Label(self.dm_data_fr, text=f'Data{i+1}').grid(row=i, column=0, sticky='w')
            ttk.Entry(self.dm_data_fr, textvariable=var, width=64).grid(row=i, column=1, sticky='we', padx=(6, 0))
            self.dm_data_vars.append(var)
        self.dm_data_fr.grid_columnconfigure(1, weight=1)

        # Hint + Buttons
        self.dm_hint_var = tk.StringVar(value='Visible cap: DM1/DMQ=8, DM2/DM4=16, DMT=6 (EDP preserves full text)')
        self.dm_hint_lbl = ttk.Label(self.dm_right_fr, textvariable=self.dm_hint_var)
        self.dm_hint_lbl.pack(anchor='w', pady=(0, 4))

        self.dm_btns_fr = ttk.Frame(self.dm_right_fr)
        self.dm_btns_fr.pack(fill=tk.X, pady=(0, 2))
        ttk.Button(self.dm_btns_fr, text='Build', command=self.build_dm_cmd).pack(side=tk.LEFT, padx=(0, 6))
        ttk.Button(self.dm_btns_fr, text='Send',
                   command=lambda: self._build_and_send(self.build_dm_cmd)).pack(side=tk.LEFT)

        # Update hint on change
        watch_vars = [self.dm_cmd_var, self.dm_timeout_var, self.dm_scrollcnt_var, *self.dm_data_vars]
        for v in watch_vars:
            v.trace_add('write', lambda *_: self._update_dm_hint())
        self._update_dm_hint()

    def _update_dm_hint(self) -> None:
        cmd = self.dm_cmd_var.get()
        cap = self._char_cap_for_display(cmd)
        nlines = 1 if cmd in ('DM1', 'DMT') else (2 if cmd == 'DM2' else 4)
        entered_lengths = [len((v.get() or '')) for v in self.dm_data_vars[:nlines]]
        self.dm_hint_var.set(
            f'Visible cap per line = {cap}. Entered lengths: {entered_lengths} (EDP keeps full text)'
        )

    def build_dm_cmd(self) -> str:
        cmd = self.dm_cmd_var.get()
        aa = (self.dm_addr_var.get() or '00').zfill(2)[-2:]
        timeout = self.dm_timeout_var.get() or '0'
        scrollcnt = self.dm_scrollcnt_var.get() or '0'
        nlines = 1 if cmd in ('DM1', 'DMT') else (2 if cmd == 'DM2' else 4)

        flash = ''.join((self.dm_flash_vars[i].get() or 'N').upper()[0] for i in range(nlines))
        slide = ''.join((self.dm_slide_vars[i].get() or 'N').upper()[0] for i in range(nlines))
        scrll = ''.join((self.dm_scroll_vars[i].get() or 'N').upper()[0] for i in range(nlines))

        def norm_color(v: str) -> str:
            # 'Space' => literal space; otherwise single color letter
            return ' ' if (v or '').strip().lower() == 'space' else (v or ' ')

        pairs: List[str] = []
        for i in range(nlines):
            fc = norm_color(self.dm_fc_vars[i].get())
            bc = norm_color(self.dm_bc_vars[i].get())
            pairs.append(f"{fc}{bc}")
        color_field = ''.join(pairs)

        parts: List[str] = [f"|{aa}{cmd}", timeout, flash, slide, scrll, scrollcnt, color_field]

        # Optional Mode/Units for DM1 and DMT
        if cmd in ('DM1', 'DMT') and self.dm_include_ann_var.get():
            parts.append(self.dm_mode_var.get() or 'G')
            parts.append(self.dm_units_var.get() or 'lb')

        # DMT traffic numeric field (names include number; insert the number only)
        if cmd == 'DMT':
            sel = self.dm_traffic_var.get() or '7 = No Icon'
            m = re.match(r'^(\d)', sel)
            traffic_code = m.group(1) if m else '7'
            parts.append(traffic_code)

        # Data fields — IMPORTANT: DO NOT TRUNCATE (EDP preserves full message)
        for i in range(nlines):
            parts.append(self.dm_data_vars[i].get() or '')

        cmd_str = '|'.join(parts) + '!'
        # Show FULL command in EDP entry
        self._fill_edp_prompt(cmd_str)
        self.log(f'BUILDER => {cmd_str}')
        return cmd_str

    def _build_and_send(self, builder_fn) -> None:
        s = builder_fn()
        if s:
            # Pass full string to handler (parsing/rendering limits are visual only)
            self.on_edp_line(s)  # defined in Section 3

    # ---- Basic display-style mutations stubs (full logic in Section 3) ----
    def set_display_color(self, name: str) -> None:
        colors = {
            'RED': '#ff3030', 'YELLOW': "#ffff40", 'GREEN': '#40ff60',
            'BLUE': '#40a0ff', 'MAGENTA': '#ff60ff', 'CYAN': '#60ffff', 'WHITE': '#ffffff',
        }
        c = colors.get(name.upper(), '#ff4040')
        try:
            for w in getattr(self, '_display_labels', []):
                w.configure(foreground=c)
        except Exception:
            pass

    def set_background_color(self, name: str) -> None:
        bgmap = {
            'NONE': '#000000', 'RED': '#300000', 'YELLOW': '#303000', 'GREEN': '#003000',
            'BLUE': '#002040', 'MAGENTA': '#300030', 'CYAN': '#003030', 'WHITE': '#ffffff',
        }
        hexval = bgmap.get((name or 'NONE').upper(), '#000000')
        self.current_bg_hex = hexval
        try:
            self.style.configure('Weight.TLabel', background=hexval, padding=0)
            self.weight_label.configure(style='Weight.TLabel')
            self.dm_canvas.configure(bg=hexval)
            self.icon_canvas.configure(bg=hexval)
        except Exception:
            pass

    def set_display_type(self, val: str) -> None:
        # Placeholder: full behavior (legacy nuances) in Section 3
        self.type_var.set(val)
        # Enable/disable legacy DO dropdown based on display type
        try:
            if (val or '').strip().lower() == 'legacy':
                self.legacy_do_cb.configure(state='readonly')
            else:
                self.legacy_do_cb.configure(state='disabled')
                self.legacy_do_var.set('Off')
        except Exception:
            pass

    def set_brightness(self, val: str) -> None:
        # Placeholder; full behavior in Section 3
        pass

    def set_mirror(self, enabled: bool) -> None:
        self.mirror = enabled

    def set_hold_weight(self, enabled: bool) -> None:
        self.hold_weight = enabled

# ------------------------------ SECTION 3/4 ------------------------------
# EDP handling, RLWS parsing, DM parsing, rendering, animations, DMT icon overlay

from typing import List, Tuple

    # ======== App methods (continued) =================================

    # ---- RLWS inbound (weight frames) --------------------------------
def on_rlws_payload(self, payload: bytes) -> None:
        now = time.time()
        self.last_data_time = now

        # If a DM is currently showing and not timed out yet, ignore live weight
        if self.display_mode == 'dm' and now < self.message_end_time:
            return

        frame_bytes = bytes([STX]) + payload + bytes([CR])
        self.log(f'RX (RLWS) hex={frame_bytes.hex(" ")}')

        pf = self.parse_rlws_payload(payload)
        if pf is None:
            self.display_invalid()
            return

        text = pf.w.strip()
        if pf.p == '-' and text and not text.startswith('-'):
            text = '-' + text

        self._ensure_mode('weight')
        self.render_weight(text, unit=pf.u, mode=pf.m, status=pf.s)
        self.last_good_weight = text

def parse_rlws_payload(self, payload: bytes) -> Optional[ParsedRLWS]:
        if len(payload) != 11:
            return None
        try:
            t = payload.decode('ascii', 'strict')
        except UnicodeDecodeError:
            return None
        p, w7, u, m, s = t[0], t[1:8], t[8], t[9], t[10]
        if p not in (' ', '-'):
            return None
        if len(w7) != 7 or sum(ch == '.' for ch in w7) > 1:
            return None
        if not all(ch.isdigit() or ch in (' ', '.') for ch in w7):
            return None
        return ParsedRLWS(p=p, w=w7, u=u, m=m, s=s)

    # ---- EDP lines + DM parsing --------------------------------------
def on_edp_line(self, line: str) -> None:
        self.log(f'EDP <= {line}')
        s = line.strip()
        # Detect DM pipe-format commands and parse
        if s.startswith('|') and ('|DM' in s[:20] or s[1:3].isdigit()):
            if self._handle_dm_command(s):
                self.log('EDP => OK')
                return

        # Fallback to EDP interpreter (variables etc.)
        if not hasattr(self, 'edp'):
            self.edp = EDP(self)
        resp = self.edp.handle(s)
        self.log(f'EDP => {resp.strip()}')
        try:
            if self.ser and getattr(self.ser, 'is_open', False):
                self.ser.write(resp.encode('ascii', 'ignore'))
        except Exception:
            pass

def _handle_dm_command(self, s: str) -> bool:
        core = s.strip()
        if core.startswith('|'):
            core = core[1:]
        parts = core.split('|')
        if parts:
            parts[-1] = parts[-1].rstrip('!')  # remove trailing '!' on last segment

        if not parts or len(parts[0]) < 5:
            return False

        head = parts[0]
        aa = head[:2]
        cmd = head[2:5].upper()
        if cmd not in ('DM1', 'DM2', 'DM4', 'DMQ', 'DMT'):
            return False

        # Timeout
        timeout = 5.0
        if len(parts) >= 2:
            try:
                timeout = max(0.001, float(parts[1]) / 1000.0)
            except ValueError:
                pass
        self.message_timeout = timeout
        self.message_end_time = time.time() + timeout

        # Flags
        flash_flags = parts[2] if len(parts) > 2 else ''
        slide_flags = parts[3] if len(parts) > 3 else ''
        scroll_flags = parts[4] if len(parts) > 4 else ''

        # lines count per mode
        nlines = 1 if cmd in ('DM1', 'DMT') else (2 if cmd == 'DM2' else 4)
        if len(parts) < 7 + nlines:
            # need at least through color field + data fields
            return False

        color_field = parts[6] if len(parts) >= 7 else ''

        # Start after color field
        idx = 7

        # ---- Robust, count-based parsing for optional fields ----
        # For DMT, traffic code must appear first among the remaining tokens.
        traffic_code = None
        if cmd == 'DMT':
            remaining = len(parts) - idx
            # shapes: [traffic] + data(nlines)  OR  [traffic] + mode + units + data(nlines)
            if remaining not in (1 + nlines, 3 + nlines):
                return False
            traffic_code = (parts[idx] or '')[:1]
            if not re.match(r'^[0-7]$', traffic_code or ''):
                return False
            idx += 1
            self.apply_dmt_traffic(traffic_code)

        # Optional Mode/Units only for DM1 and DMT
        if cmd in ('DM1', 'DMT'):
            remaining = len(parts) - idx
            # without MU: remaining == nlines
            # with MU:    remaining == 2 + nlines
            if remaining == 2 + nlines:
                # Consume MU explicitly (don't mis-take short data as MU)
                _mode = parts[idx]
                _units = parts[idx + 1]
                idx += 2
                # (We don't display MU in DM—kept for future use)

        # Remaining are EXACTLY data fields
        data = parts[idx:idx + nlines]
        while len(data) < nlines:
            data.append('')

        # Render DM and start animations
        self.render_dm_message(cmd, data, color_field)
        self._start_animations(cmd, flash_flags, slide_flags, scroll_flags)
        return True

    # ---- Traffic helpers (DMT numeric mapping) -----------------------
def apply_dmt_traffic(self, code: str) -> None:
        code = (code or '').strip()[:1]
        mapping = {
            '0': 'RED',        # Red Stop Light
            '1': 'GREEN',      # Green Go light
            '2': 'REDX',       # Red X
            '3': 'ARROWUP',    # Arrow Up
            '4': 'ARROWRIGHT', # Arrow Right
            '5': 'ARROWDOWN',  # Arrow Down
            '6': 'ARROWLEFT',  # Arrow Left
            '7': 'OFF',        # No Icon
        }
        state = mapping.get(code, 'OFF')
        self.set_icon_state(state)

    # Also support legacy DO nibble path for convenience
def handle_do(self, nibble: str) -> str:
        x = (nibble or '0')[:1]
        # In Legacy mode, map DO nibble per requested UI behavior
        try:
            is_legacy = (getattr(self, 'type_var', None) and (self.type_var.get() or '').strip().lower() == 'legacy')
        except Exception:
            is_legacy = False
        if is_legacy:
            legacy_map = {
                '0': 'OFF',          # Off
                '1': 'ARROWRIGHT',   # Green Arrow
                '2': 'GREEN',        # Green Circle
                '3': 'RED',          # Stop (red octagon)
            }
            self.set_icon_state(legacy_map.get(x, 'OFF'))
        else:
            # Default: reuse DMT numeric mapping
            self.apply_dmt_traffic(x)
        return 'OK\r\n'

    # ---- Display modes & weight rendering ----------------------------
def _ensure_mode(self, mode: str) -> None:
        if mode == self.display_mode:
            return
        if mode == 'dm':
            self.display_area.update_idletasks()
            h = max(200, self.display_area.winfo_height())
            self.display_area.configure(height=h)
            self.display_area.pack_propagate(False)
            self.weight_label.pack_forget()
            self.dm_canvas.pack(fill=tk.BOTH, expand=True)
        else:
            self.dm_canvas.pack_forget()
            self.weight_label.pack(fill=tk.BOTH, expand=True)
            self.display_area.configure(height='')
            self.display_area.pack_propagate(True)
        self.display_mode = mode

def render_weight(self, text: str, unit: str, mode: str, status: str) -> None:
        self._ensure_mode('weight')
        disp = text[::-1] if self.mirror else text
        try:
            self.weight_label.configure(text=disp)
            self.units_label.configure(text=self.label_for_unit(unit))
            self.mode_label.configure(text=mode.upper())
        except Exception:
            pass

def display_invalid(self) -> None:
        if self.hold_weight and self.last_good_weight:
            self.weight_label.configure(
                text=self.last_good_weight[::-1] if self.mirror else self.last_good_weight
            )
        else:
            self.weight_label.configure(text='--  --')
        self.units_label.configure(text='')
        self.mode_label.configure(text='')

def label_for_unit(self, u: str) -> str:
        if not hasattr(self, 'edp'):
            self.edp = EDP(self)
        return self.edp.unitdef.get(u, u)

    # ---- DM color parsing (pairs per line) ----------------------------
def _parse_dm_colors(self, color_field: str, nlines: int) -> List[Tuple[str, str]]:
        fgmap = {
            'R': "#ff3030", 'Y': "#ffff40", 'G': "#40ff60",
            'B': "#40a0ff", 'M': "#ff60ff", 'C': "#60ffff", 'W': '#ffffff',
        }
        bgmap = {
            ' ': '#000000',
            'R': "#ff3030", 'Y': "#ffff40", 'G': "#40ff60",
            'B': "#40a0ff", 'M': "#ff60ff", 'C': "#60ffff", 'W': '#ffffff',
        }
        s = (color_field or '')
        s = (s + ' ' * (2 * nlines))[:2 * nlines]
        out: List[Tuple[str, str]] = []
        for i in range(nlines):
            pair = s[2 * i:2 * i + 2]
            fc = pair[0] if len(pair) >= 1 else 'W'
            bc = pair[1] if len(pair) >= 2 else ' '
            fg = fgmap.get(fc.upper(), '#ffffff')
            bg = bgmap.get(bc.upper(), '#000000')
            out.append((fg, bg))
        return out

    # ---------------- DM RENDERING ON CANVAS --------------------------
def render_dm_message(self, cmd: str, lines_full: List[str], color_field: str) -> None:
        # Save FULL text; the renderer respects visible caps + scroll flags
        self._ensure_mode('dm')
        self._last_dm = (cmd, list(lines_full), color_field)
        self._redraw_dm()

def _fit_font_for_box(self, text: str, box_w: int, box_h: int, max_pt=72, min_pt=8) -> tkfont.Font:
        fam = 'Segoe UI'
        lo, hi = min_pt, max_pt
        best = min_pt
        # Always have at least one char to size against
        measure_text = text if text else ' '
        while lo <= hi:
            mid = (lo + hi) // 2
            f = tkfont.Font(family=fam, size=mid, weight='bold')
            tw = f.measure(measure_text)
            th = f.metrics('linespace')
            if tw <= max(1, int(box_w * 0.96)) and th <= max(1, int(box_h * 0.90)):
                best = mid
                lo = mid + 1
            else:
                hi = mid - 1
        return tkfont.Font(family=fam, size=best, weight='bold')

def _redraw_dm(self) -> None:
        if self.display_mode != 'dm' or not self._last_dm:
            return
        cmd, lines_full, color_field = self._last_dm

        c = self.dm_canvas
        try:
            c.delete('all')
        except Exception:
            return

        bg_default = self.current_bg_hex
        try:
            c.configure(bg=bg_default)
        except tk.TclError:
            pass

        W = max(1, c.winfo_width())
        H = max(1, c.winfo_height())
        pad = 6

        # visible caps per mode
        cap = self._char_cap_for_display(cmd)
        nlines = 1 if cmd in ('DM1', 'DMT') else (2 if cmd == 'DM2' else 4)

        colors = self._parse_dm_colors(color_field, nlines)
        max_pt_map = {'DMT': 170, 'DM1': 190, 'DM2': 120, 'DM4': 95, 'DMQ': 120}
        max_pt = max_pt_map.get(cmd, 140)

        def draw_text_area(text_full: str, fg: str, x_right: int, y_center: int,
                           font: tkfont.Font, line_idx: int, area_w: int, mode_right_align=True):
            # flash?
            if line_idx < len(self._flash_flags) and self._flash_flags[line_idx] == 'Y' and self.flash_state:
                fg_use = self.current_bg_hex
            else:
                fg_use = fg

            # Slide-in?
            slide_offset = 0
            if line_idx in self.slide_position:
                pos = self.slide_position[line_idx]  # 0..100
                progress = pos / 100.0
                slide_offset = int(area_w * (1.0 - progress))  # from right to final

            # Scroll?
            txt_cap = (text_full or '')[:cap]
            if (line_idx < len(self._scroll_flags) and self._scroll_flags[line_idx] == 'Y'
                    and len(text_full) > cap):
                # create a marquee across the line area
                tw = font.measure(text_full + '   ')  # small gap
                total_span = max(1, tw + area_w)
                pos_raw = self.scroll_position.get(line_idx, 0)
                pos = pos_raw % total_span  # smooth wrap based on true span
                # anchor starting at right edge + offset
                x = x_right + slide_offset
                if mode_right_align:
                    start_x = x_right - area_w + (total_span - pos)
                    c.create_text(start_x, y_center, text=text_full + '   ',
                                  font=font, fill=fg_use, anchor='w')
                else:
                    start_x = pad + (total_span - pos)
                    c.create_text(start_x, y_center, text=text_full + '   ',
                                  font=font, fill=fg_use, anchor='w')
            else:
                # non-scroll: clip to cap, align to right or left depending on area
                vis = txt_cap
                x = x_right + slide_offset
                c.create_text(x, y_center, text=vis, font=font, fill=fg_use,
                              anchor='e' if mode_right_align else 'w')

        # Layout per command
        if cmd in ('DM1', 'DMT'):
            fg, bg = colors[0]
            c.create_rectangle(0, 0, W, H, fill=bg, outline=bg)
            f = self._fit_font_for_box((lines_full[0] or '')[:max(cap, 1)], W - 2 * pad, H - 2 * pad, max_pt=max_pt)
            draw_text_area(lines_full[0], fg, W - pad, H // 2, f, 0, W - 2 * pad, mode_right_align=True)

        elif cmd == 'DM2':
            half_h = (H - 3 * pad) // 2
            # top
            fg, bg = colors[0]
            c.create_rectangle(0, 0, W, pad + half_h, fill=bg, outline=bg)
            f1 = self._fit_font_for_box((lines_full[0] or '')[:max(cap, 1)], W - 2 * pad, half_h, max_pt=max_pt)
            draw_text_area(lines_full[0], fg, W - pad, pad + half_h // 2, f1, 0, W - 2 * pad, mode_right_align=True)
            # bottom
            fg, bg = colors[1]
            c.create_rectangle(0, pad * 2 + half_h, W, H, fill=bg, outline=bg)
            f2 = self._fit_font_for_box((lines_full[1] or '')[:max(cap, 1)], W - 2 * pad, half_h, max_pt=max_pt)
            draw_text_area(lines_full[1], fg, W - pad, pad * 2 + half_h + half_h // 2,
                           f2, 1, W - 2 * pad, mode_right_align=True)

        elif cmd == 'DM4':
            cell_h = (H - 5 * pad) // 4
            for i in range(4):
                y1 = pad * i + i * cell_h
                y2 = y1 + pad + cell_h
                fg, bg = colors[i]
                c.create_rectangle(0, y1, W, y2, fill=bg, outline=bg)
                f = self._fit_font_for_box((lines_full[i] or '')[:max(cap, 1)], W - 2 * pad, cell_h, max_pt=max_pt)
                y_center = y1 + (y2 - y1) // 2
                draw_text_area(lines_full[i], fg, W - pad, y_center, f, i, W - 2 * pad, mode_right_align=True)

        elif cmd == 'DMQ':
            half_w = (W - 3 * pad) // 2
            half_h = (H - 3 * pad) // 2

            def draw_quad(idx: int, text_full: str, x: int, y: int, width: int, height: int):
                fg, bg = colors[idx]
                c.create_rectangle(x, y, x + width, y + height, fill=bg, outline=bg)
                f = self._fit_font_for_box((text_full or '')[:max(cap, 1)], width - pad, height - pad, max_pt=max_pt)
                y_center = y + height // 2
                # Right align inside each quadrant
                draw_text_area(text_full, fg, x + width - pad // 2, y_center, f, idx, width - 2 * pad, mode_right_align=True)

            draw_quad(0, lines_full[0], 0, 0, pad + half_w, pad + half_h)
            draw_quad(1, lines_full[1], pad * 2 + half_w, 0, half_w, pad + half_h)
            draw_quad(2, lines_full[2], 0, pad * 2 + half_h, pad + half_w, half_h)
            draw_quad(3, lines_full[3], pad * 2 + half_w, pad * 2 + half_h, half_w, half_h)

        # Always re-render icon overlay (if enabled) above text
        self._render_icon_canvas()

    # ---- Animations ---------------------------------------------------
def _stop_animations(self) -> None:
        for timer in (self.flash_timer, self.slide_timer, self.scroll_timer):
            if timer:
                try:
                    self.root.after_cancel(timer)
                except Exception:
                    pass
        self.flash_timer = None
        self.slide_timer = None
        self.scroll_timer = None
        self.flash_state = False
        self.slide_position.clear()
        self.scroll_position.clear()
        self._flash_flags = []
        self._slide_flags = []
        self._scroll_flags = []
        self._redraw_dm()

def _start_animations(self, cmd: str, flash_flags: str, slide_flags: str, scroll_flags: str) -> None:
        self._stop_animations()
        nlines = 1 if cmd in ('DM1', 'DMT') else (2 if cmd == 'DM2' else 4)

        def normalize_flags(flags: str, n: int) -> List[str]:
            arr = [c.upper() for c in (flags or '')[:n]]
            if len(arr) < n:
                arr += ['N'] * (n - len(arr))
            return arr

        self._flash_flags = normalize_flags(flash_flags, nlines)
        self._slide_flags = normalize_flags(slide_flags, nlines)
        self._scroll_flags = normalize_flags(scroll_flags, nlines)

        # Flash
        if any(x == 'Y' for x in self._flash_flags):
            self.flash_state = True
            self._animate_flash()

        # Slide
        for i, x in enumerate(self._slide_flags):
            if x == 'Y':
                self.slide_position[i] = 0
        if self.slide_position:
            self._animate_slide()

        # Scroll
        for i, x in enumerate(self._scroll_flags):
            if x == 'Y':
                self.scroll_position[i] = 0
        if self.scroll_position:
            self._animate_scroll()

def _animate_flash(self) -> None:
        if not any(x == 'Y' for x in self._flash_flags):
            self.flash_timer = None
            self.flash_state = False
            return
        self.flash_state = not self.flash_state
        self._redraw_dm()
        try:
            self.flash_timer = self.root.after(500, self._animate_flash)
        except tk.TclError:
            self.flash_timer = None

def _animate_slide(self) -> None:
        if not self.slide_position:
            self.slide_timer = None
            return
        for k in list(self.slide_position.keys()):
            self.slide_position[k] = min(100, self.slide_position[k] + 2)
            # after reaching 100, keep it at final position
        self._redraw_dm()
        try:
            self.slide_timer = self.root.after(30, self._animate_slide)
        except tk.TclError:
            self.slide_timer = None

def _animate_scroll(self) -> None:
        if not self.scroll_position:
            self.scroll_timer = None
            return
        # Smooth, span-aware: let values grow; renderer takes modulo by true span
        for k in list(self.scroll_position.keys()):
            self.scroll_position[k] = self.scroll_position[k] + 3
        self._redraw_dm()
        try:
            self.scroll_timer = self.root.after(25, self._animate_scroll)
        except tk.TclError:
            self.scroll_timer = None

    # ---- Small always-on icon overlay (independent of Legacy) --------
def set_icon_state(self, state: str) -> None:
        st = (state or 'OFF').upper()
        prev = getattr(self, 'icon_state', 'OFF')
        self.icon_state = st
        if st == 'OFF':
            try:
                self.icon_canvas.place_forget()
                self.icon_canvas.delete('all')
            except Exception:
                pass
            return
        # ensure visible and redrawn
        try:
            self.icon_canvas.place(x=6, y=6)  # upper-left over weight/DM area
        except Exception:
            pass
        if prev != st:
            self._render_icon_canvas()

def _render_icon_canvas(self) -> None:
        if not hasattr(self, 'icon_canvas') or self.icon_canvas is None:
            return
        st = (self.icon_state or 'OFF').upper()
        if st == 'OFF':
            try:
                self.icon_canvas.place_forget()
                self.icon_canvas.delete('all')
            except Exception:
                pass
            return

        c = self.icon_canvas
        try:
            c.delete('all')
            bg = self.current_bg_hex
            c.configure(bg=bg)
            w = int(c['width'])
            h = int(c['height'])
            cx, cy = w // 2, h // 2
            r = min(w, h) // 2 - 6

            def draw_oct(color: str) -> None:
                pts = []
                for i in range(8):
                    angle = math.pi / 8 + i * (math.pi / 4)
                    x = cx + int(r * math.cos(angle))
                    y = cy + int(r * math.sin(angle))
                    pts.append((x, y))
                flat = [p for xy in pts for p in xy]
                c.create_polygon(*flat, fill=color, outline=bg, width=2)

            def draw_red_x(color: str) -> None:
                pad = 10
                c.create_line(pad, pad, w - pad, h - pad, fill=color, width=8)
                c.create_line(w - pad, pad, pad, h - pad, fill=color, width=8)

            def draw_arrow(direction: str, color: str) -> None:
                stem_w = 8
                stem_h = 18
                head_w = 22
                head_h = 16
                if direction == 'UP':
                    c.create_rectangle(cx - stem_w // 2, cy - 2, cx + stem_w // 2, cy + stem_h,
                                       fill=color, outline=color)
                    c.create_polygon(cx, cy - head_h, cx - head_w // 2, cy, cx + head_w // 2, cy,
                                     fill=color, outline=color)
                elif direction == 'DOWN':
                    c.create_rectangle(cx - stem_w // 2, cy - stem_h, cx + stem_w // 2, cy + 2,
                                       fill=color, outline=color)
                    c.create_polygon(cx, cy + head_h, cx - head_w // 2, cy, cx + head_w // 2, cy,
                                     fill=color, outline=color)
                elif direction == 'RIGHT':
                    c.create_rectangle(cx - stem_h, cy - stem_w // 2, cx + 2, cy + stem_w // 2,
                                       fill=color, outline=color)
                    c.create_polygon(cx + head_h, cy, cx, cy - head_w // 2, cx, cy + head_w // 2,
                                     fill=color, outline=color)
                elif direction == 'LEFT':
                    c.create_rectangle(cx - 2, cy - stem_w // 2, cx + stem_h, cy + stem_w // 2,
                                       fill=color, outline=color)
                    c.create_polygon(cx - head_h, cy, cx, cy - head_w // 2, cx, cy + head_w // 2,
                                     fill=color, outline=color)

            if st == 'GREEN':
                draw_oct('#40ff80')
            elif st == 'RED':
                draw_oct('#ff4040')
            elif st == 'REDX':
                draw_red_x('#ff4040')
            elif st == 'ARROWUP':
                draw_arrow('UP', '#40ff80')
            elif st == 'ARROWRIGHT':
                draw_arrow('RIGHT', '#40ff80')
            elif st == 'ARROWDOWN':
                draw_arrow('DOWN', '#40ff80')
            elif st == 'ARROWLEFT':
                draw_arrow('LEFT', '#40ff80')
        except Exception:
            pass

# ---- Brightness & color tweaks -----------------------------------
def set_display_color(self, name: str) -> None:
        # Keep labels legible against background
        colors = {
            'RED': '#ff3030', 'YELLOW': "#ffff40", 'GREEN': '#40ff60',
            'BLUE': '#40a0ff', 'MAGENTA': '#ff60ff', 'CYAN': '#60ffff', 'WHITE': '#ffffff',
        }
        c = colors.get((name or '').upper(), '#ff4040')

        def _hex_to_rgb(h):
            h = h.lstrip('#')
            return tuple(int(h[i:i+2], 16) for i in (0, 2, 4))

        fg_rgb = _hex_to_rgb(c)
        bg_rgb = _hex_to_rgb(self.current_bg_hex)
        luma = lambda rgb: 0.2126 * rgb[0] + 0.7152 * rgb[1] + 0.0722 * rgb[2]
        dist = sum(abs(fg_rgb[i] - bg_rgb[i]) for i in range(3))
        if dist < 120 or abs(luma(fg_rgb) - luma(bg_rgb)) < 40:
            c = '#ffffff' if luma(bg_rgb) < 128 else '#000000'

        for w in getattr(self, '_display_labels', []):
            try:
                w.configure(foreground=c)
            except Exception:
                pass

        if self.display_mode == 'dm':
            self._redraw_dm()

def set_brightness(self, val: str) -> None:
        try:
            if (val or '').upper() == 'DAYLVL':
                level = 4
            else:
                level = max(1, min(6, int(val)))
        except Exception:
            level = 4
        base = (getattr(self, 'color_var', None) and self.color_var.get()) or 'Red'
        base_map = {
            'Red': (255, 48, 48), 'Yellow': (255, 255, 64), 'Green': (64, 255, 96),
            'Blue': (64, 160, 255), 'Magenta': (255, 96, 255), 'Cyan': (96, 255, 255), 'White': (255, 255, 255),
        }
        r, g, b = base_map.get(base, (255, 64, 64))
        k = 0.25 + 0.15 * (level - 1)
        rgb = (int(r * k), int(g * k), int(b * k))
        c = f'#{rgb[0]:02x}{rgb[1]:02x}{rgb[2]:02x}'
        for w in getattr(self, '_display_labels', []):
            try:
                w.configure(foreground=c)
            except Exception:
                pass
        if self.display_mode == 'dm':
            self._redraw_dm()

    # ---- No-data watchdog --------------------------------------------
def _update_no_data_check(self) -> None:
        if not hasattr(self, 'last_data_time'):
            self.last_data_time = 0.0
        if (time.time() - self.last_data_time) > 3.0 and self.display_mode == 'weight':
            if self.hold_weight and self.last_good_weight:
                self.weight_label.configure(
                    text=self.last_good_weight[::-1] if self.mirror else self.last_good_weight
                )
            else:
                self.weight_label.configure(text='NO DATA')
                self.units_label.configure(text='')
                self.mode_label.configure(text='')
        try:
            self.root.after(500, self._update_no_data_check)
        except Exception:
            pass

# ------------------------------ SECTION 4/4 ------------------------------
# Final utilities (none redefined) and bootstrap

def main() -> None:
    root = tk.Tk()
    try:
        # Keep Tk scaling predictable across DPI
        root.tk.call('tk', 'scaling', 1.0)
    except tk.TclError:
        pass

    app = App(root)

    # Initial visual setup
    try:
        app.set_background_color('NONE')
        # Ensure the small icon overlay exists and is hidden initially
        if getattr(app, 'icon_canvas', None) is not None:
            app.set_icon_state('OFF')
        # Keyboard shortcut for quick minimize (Ctrl+M)
        try:
            app.root.bind('<Control-m>', lambda e: app.minimize_window())
        except Exception:
            pass
    except Exception:
        pass

    # Start watchdog
    try:
        app._update_no_data_check()
    except Exception:
        pass

    root.mainloop()


if __name__ == '__main__':
    # Bind Section 3 functions onto App as methods (ensures UI calls work)
    try:
        App.on_rlws_payload = on_rlws_payload                 # type: ignore[attr-defined]
        App.parse_rlws_payload = parse_rlws_payload           # type: ignore[attr-defined]
        App.on_edp_line = on_edp_line                         # type: ignore[attr-defined]
        App._handle_dm_command = _handle_dm_command           # type: ignore[attr-defined]
        App.apply_dmt_traffic = apply_dmt_traffic             # type: ignore[attr-defined]
        App.handle_do = handle_do                             # type: ignore[attr-defined]
        App._ensure_mode = _ensure_mode                       # type: ignore[attr-defined]
        App.render_weight = render_weight                     # type: ignore[attr-defined]
        App.display_invalid = display_invalid                 # type: ignore[attr-defined]
        App.label_for_unit = label_for_unit                   # type: ignore[attr-defined]
        App._parse_dm_colors = _parse_dm_colors               # type: ignore[attr-defined]
        App.render_dm_message = render_dm_message             # type: ignore[attr-defined]
        App._fit_font_for_box = _fit_font_for_box             # type: ignore[attr-defined]
        App._redraw_dm = _redraw_dm                           # type: ignore[attr-defined]
        App._stop_animations = _stop_animations               # type: ignore[attr-defined]
        App._start_animations = _start_animations             # type: ignore[attr-defined]
        App._animate_flash = _animate_flash                   # type: ignore[attr-defined]
        App._animate_slide = _animate_slide                   # type: ignore[attr-defined]
        App._animate_scroll = _animate_scroll                 # type: ignore[attr-defined]
        App.set_icon_state = set_icon_state                   # type: ignore[attr-defined]
        App._render_icon_canvas = _render_icon_canvas         # type: ignore[attr-defined]
        App.set_display_color = set_display_color             # type: ignore[attr-defined]
        App.set_brightness = set_brightness                   # type: ignore[attr-defined]
        App._update_no_data_check = _update_no_data_check     # type: ignore[attr-defined]
    except Exception:
        # If binding fails during import-time (e.g., missing defs), continue; UI may still run.
        pass
    main()
