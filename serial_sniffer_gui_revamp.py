"""
Serial sniffer GUI using pyserial and tkinter.
"""

import threading
import datetime
import os
import time
import json

import tkinter as tk
from tkinter import ttk, messagebox, filedialog

# Try to import pyserial's Serial and SerialException
try:
    import serial
    from serial import Serial as _Serial
    from serial import SerialException
    import serial.tools.list_ports
    SerialClass = _Serial
except ImportError:
    serial = None
    SerialClass = None
    class SerialException(Exception):
        """Fallback if pyserial is not installed."""

CONFIG_FILE = "serial_sniffer_config.json"


class SerialSnifferApp:
    """Main application window for the Python Serial Sniffer."""

    def __init__(self, master):
        """Initialize the GUI, load config, and set up state."""
        self.master = master
        master.title("Python Serial Sniffer")
        master.geometry("950x700")

        # runtime state
        self.running = False
        self.paused = False
        self.auto_sending = False

        self.ser_a = None
        self.ser_b = None
        self.bytes_a_to_b = 0
        self.bytes_b_to_a = 0

        # store raw entries for dynamic reformat
        self.data_buffer = []  # list of (ts, direction, data_bytes)

        # UI variables
        self.port_a = tk.StringVar()
        self.port_b = tk.StringVar()
        self.baudrate = tk.StringVar(value="9600")
        self.databits = tk.StringVar(value="8")
        self.parity = tk.StringVar(value="None")
        self.stopbits = tk.StringVar(value="1")
        self.dark_mode = tk.BooleanVar(value=True)
        self.display_mode = tk.StringVar(value="BIN")
        self.send_port = tk.StringVar(value="A")
        self.auto_send_interval = tk.StringVar(value="1.0")
        self.enable_port_a = tk.BooleanVar(value=True)
        self.enable_port_b = tk.BooleanVar(value=True)

        # persist last command
        self.last_command = ""

        self.log_file = "serial_sniffer_rawlog.txt"

        # auto-send warning flags
        self._warn_no_cmd = False
        self._warn_not_conn = False

        # will store current text fg for refresh
        self._text_fg = "#000000"

        # load config (including last_command)
        self.load_config()

        # build UI
        self.create_widgets()

        # restore last command
        if self.last_command:
            self.entry_command.insert(0, self.last_command)

        # fill port lists, apply theme
        self.update_ports()
        self.apply_theme()

        master.protocol("WM_DELETE_WINDOW", self.on_exit)

        def create_widgets(self):
            """Create and place all the widgets in the window."""
            notebook = ttk.Notebook(self.master)
            notebook.pack(expand=True, fill="both")

            tab_conn = ttk.Frame(notebook)
            tab_monitor = ttk.Frame(notebook)
            notebook.add(tab_conn, text="Connection")
            notebook.add(tab_monitor, text="Monitor")

            # --- Connection tab ---
            frm_top = ttk.LabelFrame(tab_conn, text="Port Configuration")
            frm_top.pack(fill="x", padx=10, pady=10)

            ttk.Label(frm_top, text="Port A:").grid(row=0, column=0, sticky="w")
            self.combo_a = ttk.Combobox(frm_top, textvariable=self.port_a, width=10)
            self.combo_a.grid(row=0, column=1, padx=5)
            ttk.Checkbutton(frm_top, text="Enable Port A", variable=self.enable_port_a).grid(row=1, column=1, sticky="w")

            ttk.Label(frm_top, text="Port B:").grid(row=0, column=2, sticky="w")
            self.combo_b = ttk.Combobox(frm_top, textvariable=self.port_b, width=10)
            self.combo_b.grid(row=0, column=3, padx=5)
            ttk.Checkbutton(frm_top, text="Enable Port B", variable=self.enable_port_b).grid(row=1, column=3, sticky="w")

            ttk.Label(frm_top, text="Baud:").grid(row=0, column=4, sticky="w")
            self.combo_baud = ttk.Combobox(
                frm_top,
                textvariable=self.baudrate,
                values=["300", "1200", "2400", "4800", "9600", "19200", "38400", "57600", "115200"],
                width=8,
            )
            self.combo_baud.grid(row=0, column=5, padx=5)

            ttk.Label(frm_top, text="Data Bits:").grid(row=0, column=6, sticky="w")
            self.combo_data = ttk.Combobox(
                frm_top,
                textvariable=self.databits,
                values=["5", "6", "7", "8"],
                width=5,
            )
            self.combo_data.grid(row=0, column=7, padx=5)

            ttk.Label(frm_top, text="Parity:").grid(row=0, column=8, sticky="w")
            self.combo_parity = ttk.Combobox(
                frm_top,
                textvariable=self.parity,
                values=["None", "Even", "Odd", "Mark", "Space"],
                width=5,
            )
            self.combo_parity.grid(row=0, column=9, padx=5)

            ttk.Label(frm_top, text="Stop Bits:").grid(row=0, column=10, sticky="w")
            self.combo_stop = ttk.Combobox(
                frm_top,
                textvariable=self.stopbits,
                values=["1", "1.5", "2"],
                width=5,
            )
            self.combo_stop.grid(row=0, column=11, padx=5)

            frm_btns = ttk.Frame(tab_conn)
            frm_btns.pack(fill="x", padx=10, pady=5)
            self.btn_connect = ttk.Button(frm_btns, text="Connect", command=self.connect_serial)
            self.btn_disconnect = ttk.Button(frm_btns, text="Disconnect", command=self.disconnect_serial, state="disabled")
            self.btn_pause = ttk.Button(frm_btns, text="Pause Text", command=self.toggle_pause, state="disabled")
            self.btn_resume = ttk.Button(frm_btns, text="Resume Text", command=self.toggle_resume, state="disabled")
            self.btn_export = ttk.Button(frm_btns, text="Export Log", command=self.export_log)
            self.btn_clear_disp = ttk.Button(frm_btns, text="Clear Text", command=self.clear_display)
            ttk.Checkbutton(frm_btns, text="Dark Mode", variable=self.dark_mode, command=self.apply_theme).grid(row=0, column=7, padx=10)
            self.btn_connect.grid(row=0, column=0, padx=5)
            self.btn_disconnect.grid(row=0, column=1, padx=5)
            self.btn_pause.grid(row=0, column=2, padx=5)
            self.btn_resume.grid(row=0, column=3, padx=5)
            self.btn_export.grid(row=0, column=6, padx=5)
            self.btn_clear_disp.grid(row=0, column=5, padx=5)

            # --- Monitor tab ---
            frm_fmt = ttk.Frame(tab_monitor)
            frm_fmt.pack(fill="x", padx=10, pady=5)
            ttk.Label(frm_fmt, text="Display Format:").pack(side="left")
            self.format_buttons = {}
            for mode in ("BIN", "HEX", "DEC", "ASCII"):
                btn = ttk.Button(frm_fmt, text=mode, command=lambda m=mode: self.set_display_mode(m))
                btn.pack(side="left", padx=5)
                self.format_buttons[mode] = btn
            self.highlight_display_mode_button()

            self.text_display = tk.Text(tab_monitor, wrap="none", state="disabled", height=20)
            self.text_display.pack(expand=True, fill="both", padx=10, pady=(2, 5))
            scroll_y = ttk.Scrollbar(self.text_display, orient="vertical", command=self.text_display.yview)
            scroll_x = ttk.Scrollbar(self.text_display, orient="horizontal", command=self.text_display.xview)
            self.text_display.configure(yscrollcommand=scroll_y.set, xscrollcommand=scroll_x.set)
            scroll_y.pack(side="right", fill="y")
            scroll_x.pack(side="bottom", fill="x")

            frm_cnt = ttk.Labelframe(tab_monitor, text="Bytes Counter")
            frm_cnt.pack(fill="x", padx=10, pady=(0, 10))
            self.label_a_to_b = ttk.Label(frm_cnt, text="A → B Bytes: 0", font=("Arial", 13))
            self.label_b_to_a = ttk.Label(frm_cnt, text="B → A Bytes: 0", font=("Arial", 13))
            self.label_total = ttk.Label(frm_cnt, text="Total Bytes: 0", font=("Arial", 13))
            ttk.Button(frm_cnt, text="Reset Counter", command=self.reset_counter, width=16).pack(side="right")
            self.label_a_to_b.pack(side="left", padx=(0, 120))
            self.label_b_to_a.pack(side="left", padx=(0, 120))
            self.label_total.pack(side="left", padx=(0, 120))

            frm_send = ttk.Labelframe(tab_monitor, text="Send Command")
            frm_send.pack(fill="x", padx=10, pady=5)
            ttk.Label(frm_send, text="Command:").grid(row=0, column=0, sticky="sw", padx=0, pady=0)

            self.btn_send_it = tk.Button(
                frm_send,
                text="SEND IT",
                fg="white",
                bg="red",
                font=("Arial", 12, "bold"),
                command=self.send_command,
            )
            self.btn_send_it.grid(row=0, column=5, sticky="sw", padx=6, pady=0)

            self.btn_clear = ttk.Button(frm_send, text="Clear", command=lambda: self.entry_command.delete(0, tk.END))
            self.btn_clear.grid(row=0, column=6, padx=0, pady=0)

            self.entry_command = tk.Entry(frm_send, width=40)
            self.entry_command.grid(row=0, column=1, sticky="sw", padx=0, pady=0)
            self.entry_command.bind("<Return>", lambda e: (self.send_command(), "break"))

            ttk.Label(frm_send, text="").grid(row=0, column=2, sticky="nw", padx=0, pady=0)
            ttk.Combobox(frm_send, textvariable=self.send_port, values=("A", "B"), width=5).grid(row=0, column=2, sticky="sw", padx=6, pady=0)

            ttk.Label(frm_send, text="Interval (s):").grid(row=3, column=1, sticky="w", padx=5, pady=5)
            ttk.Entry(frm_send, textvariable=self.auto_send_interval, width=10).grid(row=3, column=1, sticky="w", padx=50, pady=25)

            self.btn_auto_send = ttk.Button(frm_send, text="Start Auto-Send", command=self.toggle_auto_send)
            self.btn_auto_send.grid(row=3, column=0, padx=5, pady=5)

    def clear_display(self):
        """Clear the display and internal buffer, retain text color."""
        self.data_buffer.clear()
        self.text_display.config(state="normal", foreground=self._text_fg)
        self.text_display.delete("1.0", "end")
        self.text_display.config(state="disabled")

    def load_config(self):
        """Load settings (including last command) from JSON config."""
        if not os.path.exists(CONFIG_FILE):
            return
        try:
            with open(CONFIG_FILE, "r", encoding="utf-8") as f:
                cfg = json.load(f)
        except (OSError, json.JSONDecodeError):
            return

        for key, var in (
            ("port_a", self.port_a), ("port_b", self.port_b),
            ("baudrate", self.baudrate), ("databits", self.databits),
            ("parity", self.parity), ("stopbits", self.stopbits),
            ("dark_mode", self.dark_mode),
            ("display_mode", self.display_mode),
            ("send_port", self.send_port),
            ("auto_send_interval", self.auto_send_interval),
            ("enable_port_a", self.enable_port_a),
            ("enable_port_b", self.enable_port_b),
        ):
            if key in cfg:
                var.set(cfg[key])
        self.last_command = cfg.get("last_command", "")

    def save_config(self):
        """Save current settings (and last command) to JSON config."""
        cfg = {
            "port_a": self.port_a.get(),
            "port_b": self.port_b.get(),
            "baudrate": self.baudrate.get(),
            "databits": self.databits.get(),
            "parity": self.parity.get(),
            "stopbits": self.stopbits.get(),
            "dark_mode": self.dark_mode.get(),
            "display_mode": self.display_mode.get(),
            "send_port": self.send_port.get(),
            "auto_send_interval": self.auto_send_interval.get(),
            "enable_port_a": self.enable_port_a.get(),
            "enable_port_b": self.enable_port_b.get(),
            "last_command": self.entry_command.get().strip(),
        }
        try:
            with open(CONFIG_FILE, "w", encoding="utf-8") as f:
                json.dump(cfg, f, indent=4)
        except OSError:
            print("Failed to save config.")

    def on_exit(self):
        """Clean up on close: save config, clear log, and exit."""
        self.save_config()
        self.running = False
        try:
            if self.ser_a and self.ser_a.is_open:
                self.ser_a.close()
            if self.ser_b and self.ser_b.is_open:
                self.ser_b.close()
        except SerialException:
            pass
        open(self.log_file, "w", encoding="utf-8").close()
        self.master.destroy()

    def update_ports(self):
        """Refresh the available serial ports list."""
        ports = []
        if serial is not None:
            try:
                ports = [p.device for p in serial.tools.list_ports.comports()]
            except SerialException:
                ports = []
        self.combo_a["values"] = ports
        self.combo_b["values"] = ports

    def connect_serial(self):
        """Open serial connections with the configured parameters."""
        if SerialClass is None:
            messagebox.showerror(
                "PySerial Error",
                "Cannot load pyserial's Serial class.\n"
                "Ensure pyserial is installed and no local serial.py is shadowing it."
            )
            return
        try:
            p_char = self.parity.get()[0].upper()
            b_size = int(self.databits.get())
            s_bits = float(self.stopbits.get())
            baud = int(self.baudrate.get())

            if self.enable_port_a.get():
                self.ser_a = SerialClass(
                    port=self.port_a.get(),
                    baudrate=baud,
                    bytesize=b_size,
                    parity=p_char,
                    stopbits=s_bits,
                    timeout=0
                )
            if self.enable_port_b.get():
                self.ser_b = SerialClass(
                    port=self.port_b.get(),
                    baudrate=baud,
                    bytesize=b_size,
                    parity=p_char,
                    stopbits=s_bits,
                    timeout=0
                )
            if not (self.ser_a or self.ser_b):
                messagebox.showwarning(
                    "Warning", "At least one port must be enabled."
                )
                return

            self.running = True
            self.btn_connect["state"] = "disabled"
            self.btn_disconnect["state"] = "normal"
            self.btn_pause["state"] = "normal"
            threading.Thread(
                target=self.read_serial, daemon=True
            ).start()
        except SerialException as e:
            messagebox.showerror("Error", f"Connection failed: {e}")

    def disconnect_serial(self):
        """Close any open serial connections."""
        self.running = False
        try:
            if self.ser_a and self.ser_a.is_open:
                self.ser_a.close()
            if self.ser_b and self.ser_b.is_open:
                self.ser_b.close()
        except SerialException:
            pass
        self.btn_disconnect["state"] = "disabled"
        self.btn_connect["state"] = "normal"
        self.btn_pause["state"] = "disabled"
        self.btn_resume["state"] = "disabled"

    def read_serial(self):
        """Continuously read from A→B and B→A."""
        while self.running:
            try:
                da = (
                    self.ser_a.read(self.ser_a.in_waiting or 1)
                    if self.ser_a and self.ser_a.is_open else b""
                )
                db = (
                    self.ser_b.read(self.ser_b.in_waiting or 1)
                    if self.ser_b and self.ser_b.is_open else b""
                )
                if da:
                    if self.ser_b and self.ser_b.is_open:
                        self.ser_b.write(da)
                    self.bytes_a_to_b += len(da)
                    ts = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                    self.data_buffer.append((ts, "A→B", da))
                    self._append_display(ts, "A→B", da)
                if db:
                    if self.ser_a and self.ser_a.is_open:
                        self.ser_a.write(db)
                    self.bytes_b_to_a += len(db)
                    ts = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
                    self.data_buffer.append((ts, "B→A", db))
                    self._append_display(ts, "B→A", db)
            except SerialException:
                pass
            time.sleep(0.01)

    def _append_display(self, ts, direction, data):
        """Internal: append one record to UI and log file."""
        fmt = self.format_data(data, self.display_mode.get())
        msg = f"{ts} | {direction}: {fmt}\n"
        with open(self.log_file, "a", encoding="utf-8") as f:
            f.write(msg)

        if not self.paused:
            self.text_display.config(state="normal", foreground=self._text_fg)
            start = self.text_display.index("end-1c")
            self.text_display.insert("end", msg)
            end = self.text_display.index("end-1c")

            if direction.startswith("Sent"):
                self.text_display.tag_add("sent", start, end)
            elif direction.startswith("A→B"):
                self.text_display.tag_add("portA", start, end)
            else:
                self.text_display.tag_add("portB", start, end)

            self.text_display.see("end")
            self.text_display.config(state="disabled")

        self.update_byte_counter()

    def refresh_display(self):
        """Re-render entire buffer when display_mode changes."""
        self.text_display.config(state="normal", foreground=self._text_fg)
        self.text_display.delete("1.0", "end")
        for ts, direction, data in self.data_buffer:
            fmt = self.format_data(data, self.display_mode.get())
            msg = f"{ts} | {direction}: {fmt}\n"
            self.text_display.insert("end", msg)
            start = f"end-{len(msg)}c"
            if direction.startswith("Sent"):
                self.text_display.tag_add("sent", start, "end")
            elif direction.startswith("A→B"):
                self.text_display.tag_add("portA", start, "end")
            else:
                self.text_display.tag_add("portB", start, "end")
        self.text_display.see("end")
        self.text_display.config(state="disabled")

    def format_data(self, data, mode):
        """Format bytes in BIN, HEX, DEC, or ASCII."""
        if mode == "HEX":
            return data.hex()
        if mode == "DEC":
            return " ".join(str(b) for b in data)
        if mode == "ASCII":
            return data.decode(errors="replace")
        return " ".join(bin(b)[2:].zfill(8) for b in data)

    def export_log(self):
        """Export the raw log file under a user-chosen name."""
        path = filedialog.asksaveasfilename(defaultextension=".txt")
        if not path:
            return
        try:
            os.replace(self.log_file, path)
            open(self.log_file, "w", encoding="utf-8").close()
        except OSError as e:
            messagebox.showerror("Error", f"Failed to export log: {e}")

    def toggle_pause(self):
        """Pause appending incoming data to the display."""
        self.paused = True
        self.btn_pause["state"] = "disabled"
        self.btn_resume["state"] = "normal"

    def toggle_resume(self):
        """Resume appending incoming data to the display."""
        self.paused = False
        self.btn_pause["state"] = "normal"
        self.btn_resume["state"] = "disabled"

    def reset_counter(self):
        """Reset byte counters to zero."""
        self.bytes_a_to_b = 0
        self.bytes_b_to_a = 0
        self.update_byte_counter()

    def update_byte_counter(self):
        """Refresh the byte counters in the UI."""
        total = self.bytes_a_to_b + self.bytes_b_to_a
        self.label_a_to_b.config(text=f"A → B Bytes: {self.bytes_a_to_b}")
        self.label_b_to_a.config(text=f"B → A Bytes: {self.bytes_b_to_a}")
        self.label_total.config(text=f"Total Bytes: {total}")

    def send_command(self):
        """Send the text from the entry to the selected port."""
        cmd = self.entry_command.get().strip()
        if not cmd:
            if not self.auto_sending or (self.auto_sending and not self._warn_no_cmd):
                messagebox.showwarning("Warning", "Please enter a command.")
                self._warn_no_cmd = True
            return
        self._warn_no_cmd = False
        self._send_to_port(cmd + "\r\n")

    def _send_to_port(self, text):
        """Helper to send raw text to either port A or B."""
        data = text.encode()
        port = self.ser_a if self.send_port.get() == "A" else self.ser_b

        if not port or not getattr(port, "is_open", False):
            if not self.auto_sending or (self.auto_sending and not self._warn_not_conn):
                messagebox.showerror("Error", f"Port {self.send_port.get()} not connected")
                self._warn_not_conn = True
            return
        self._warn_not_conn = False

        if (port is self.ser_a and not self.enable_port_a.get()) or \
           (port is self.ser_b and not self.enable_port_b.get()):
            messagebox.showerror("Error", f"Port {self.send_port.get()} is disabled.")
            return

        try:
            port.write(data)
            ts = datetime.datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            self.data_buffer.append((ts, f"Sent to {self.send_port.get()}", data))
            self._append_display(ts, f"Sent to {self.send_port.get()}", data)
        except SerialException as e:
            messagebox.showerror("Error", f"Send failed: {e}")

    def toggle_auto_send(self):
        """Start or stop automatic periodic sending."""
        self.auto_sending = not self.auto_sending
        self.btn_auto_send.config(
            text="Stop Auto-Send" if self.auto_sending else "Start Auto-Send"
        )
        if self.auto_sending:
            self._warn_no_cmd = False
            self._warn_not_conn = False
            self._auto_send_loop()

    def _auto_send_loop(self):
        """Internal loop for automatic sending based on interval."""
        if not self.auto_sending:
            return
        self.send_command()
        try:
            interval = float(self.auto_send_interval.get())
        except ValueError:
            interval = 1.0
        self.master.after(int(interval * 1000), self._auto_send_loop)

    def set_display_mode(self, mode):
        """Switch display formatting mode and refresh only."""
        self.display_mode.set(mode)
        self.highlight_display_mode_button()
        self.refresh_display()

    def highlight_display_mode_button(self):
        """Visually press the selected display mode button."""
        for m, btn in self.format_buttons.items():
            btn.state(["pressed"] if m == self.display_mode.get() else ["!pressed"])

    def apply_theme(self):
        """Apply light/dark theme to all widgets and lock Checkbutton colors."""
        style = ttk.Style(self.master)
        style.theme_use("clam")

        if self.dark_mode.get():
            bg, fg_btn, fg_cmb = "#222222", "#00ff00", "#ffa500"
            text_bg, text_fg = "#1e1e1e", "#eeeeee"
        else:
            bg, fg_btn, fg_cmb = "#f0f0f0", "#000300", "#120800"
            text_bg, text_fg = "#ffffff", "#000000"

        # remember this for later refresh_display calls
        self._text_fg = text_fg

        self.master.configure(bg=bg)
        style.configure("TLabel", background=bg, foreground=text_fg)
        style.configure("TFrame", background=bg)
        style.configure("TLabelframe", background=bg, foreground=text_fg)
        style.configure("TLabelframe.Label", background=bg, foreground=text_fg)
        style.configure("TButton", background=bg, foreground=fg_btn)
        style.configure("TCheckbutton", background=bg, foreground=text_fg)
        style.configure("TCombobox",
                        fieldbackground=text_bg,
                        background=text_bg,
                        foreground=fg_cmb,
                        arrowcolor=fg_cmb)

        # Prevent Checkbuttons from changing color on hover/active
        style.map("TCheckbutton",
                  background=[("active", bg), ("!active", bg)],
                  foreground=[("active", text_fg), ("!active", text_fg)])

        # apply to the text display and other widgets
        for w in (
            self.text_display,
            self.combo_a,
            self.combo_b,
            self.combo_baud,
            self.combo_data,
            self.combo_parity,
            self.combo_stop
        ):
            try:
                w.config(background=text_bg, foreground=text_fg)
            except tk.TclError:
                pass

        # command entry background & cursor
        self.entry_command.config(
            bg=text_bg,
            fg=text_fg,
            insertbackground=text_fg
        )

        # tag colors for incoming/sent
        style_portA = "#ff5555" if self.dark_mode.get() else "red"
        style_portB = "#b6c8f8" if self.dark_mode.get() else "black"
        style_sent  = "#BCF8A4" if self.dark_mode.get() else "#00008B"

        self.text_display.tag_config("portA", foreground=style_portA)
        self.text_display.tag_config("portB", foreground=style_portB)
        self.text_display.tag_config("sent",  foreground=style_sent)


if __name__ == "__main__":
    root = tk.Tk()
    app = SerialSnifferApp(root)
    root.mainloop()
