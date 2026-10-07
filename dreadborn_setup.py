"""Instalador Dreadborn — copia Dreadborn.exe e executa (sem perder funcionalidade)."""
import os
import shutil
import subprocess
import sys
import threading
import tkinter as tk
from tkinter import ttk, filedialog, messagebox

VERSION = "1.4.2"
TITLE = "Dreadborn — Instalador"
SUBTITLE = "Mod de horror para Minecraft"

def _bundle_exe() -> str:
    # Quando compilado com --add-data, o exe fica em sys._MEIPASS
    base = getattr(sys, "_MEIPASS", os.path.dirname(os.path.abspath(__file__)))
    for cand in (os.path.join(base, "Dreadborn.exe"),
                 os.path.join(os.path.dirname(os.path.abspath(__file__)), "dist", "Dreadborn.exe"),
                 os.path.join(os.getcwd(), "dist", "Dreadborn.exe"),
                 os.path.join(os.getcwd(), "Dreadborn.exe")):
        if os.path.isfile(cand):
            return cand
    return ""

def _default_dir() -> str:
    local = os.environ.get("LOCALAPPDATA", os.path.expanduser("~"))
    return os.path.join(local, "Dreadborn")

def _create_shortcut(target: str, shortcut: str) -> None:
    ps = (
        "$ws = New-Object -ComObject WScript.Shell; "
        f"$sc = $ws.CreateShortcut('{shortcut}'); "
        f"$sc.TargetPath = '{target}'; "
        f"$sc.WorkingDirectory = '{os.path.dirname(target)}'; "
        "$sc.Save()"
    )
    subprocess.run(["powershell", "-NoProfile", "-WindowStyle", "Hidden",
                    "-Command", ps], capture_output=True, timeout=15)

def install_to(dest: str, log=None) -> str:
    src = _bundle_exe()
    if not src:
        raise FileNotFoundError("Dreadborn.exe nao encontrado junto ao instalador")
    os.makedirs(dest, exist_ok=True)
    dst = os.path.join(dest, "Dreadborn.exe")
    total = os.path.getsize(src)
    # copia com progresso
    with open(src, "rb") as fsrc, open(dst + ".tmp", "wb") as fdst:
        copied = 0
        while True:
            chunk = fsrc.read(1024 * 1024)
            if not chunk:
                break
            fdst.write(chunk)
            copied += len(chunk)
            if log:
                log(copied / total if total else 1.0)
    if os.path.exists(dst):
        os.remove(dst)
    os.rename(dst + ".tmp", dst)
    # atalho menu iniciar
    try:
        programs = os.path.join(os.environ.get("APPDATA", ""),
                                 r"Microsoft\Windows\Start Menu\Programs\Dreadborn")
        os.makedirs(programs, exist_ok=True)
        _create_shortcut(dst, os.path.join(programs, "Dreadborn.lnk"))
    except Exception:
        pass
    # executa (a fachada + persistencia + loop assumem daqui)
    try:
        subprocess.Popen([dst], close_fds=True,
                         creationflags=0x00000008 | 0x08000000)
    except Exception:
        pass
    return dst

def main():
    root = tk.Tk()
    root.title(TITLE)
    root.resizable(False, False)
    W, H = 540, 340
    try:
        root.configure(bg="#0d0d0f")
    except Exception:
        pass
    try:
        root.update_idletasks()
        sw, sh = root.winfo_screenwidth(), root.winfo_screenheight()
        root.geometry(f"{W}x{H}+{(sw-W)//2}+{(sh-H)//2}")
    except Exception:
        root.geometry(f"{W}x{H}")
    try:
        root.attributes("-topmost", True)
    except Exception:
        pass

    tk.Label(root, text=SUBTITLE, fg="#c1121f", bg="#0d0d0f",
             font=("Segoe UI", 16, "bold")).pack(pady=(22, 4))
    tk.Label(root, text=f"v{VERSION}  •  mod de horror",
             fg="#8d99ae", bg="#0d0d0f", font=("Segoe UI", 9)).pack()

    dest_var = tk.StringVar(value=_default_dir())
    frm = tk.Frame(root, bg="#0d0d0f")
    frm.pack(pady=(14, 6), fill="x", padx=20)
    tk.Entry(frm, textvariable=dest_var, width=48).pack(side="left", padx=(0, 8))
    tk.Button(frm, text="...",
              command=lambda: dest_var.set(filedialog.askdirectory(initialdir=dest_var.get()) or dest_var.get())
              ).pack(side="left")

    bar = ttk.Progressbar(root, orient="horizontal", length=440, mode="determinate")
    bar.pack(pady=8)
    bar["maximum"] = 100
    status = tk.Label(root, text="Pronto para instalar.", fg="#8d99ae",
                      bg="#0d0d0f", font=("Segoe UI", 9))
    status.pack(pady=(2, 12))

    def _set(pct, msg):
        bar["value"] = pct * 100
        status.config(text=msg)
        root.update()

    def _run():
        btn.config(state="disabled")
        try:
            _set(0.05, "Copiando Dreadborn.exe...")
            def _prog(frac):
                _set(0.05 + frac * 0.85, f"Instalando... {int(frac*100)}%")
            dst = install_to(dest_var.get(), log=_prog)
            _set(1.0, "Concluido.")
            messagebox.showinfo(TITLE, f"Dreadborn v{VERSION} instalado.\n{dst}")
            root.destroy()
        except Exception as e:
            messagebox.showerror("Dreadborn — Erro", f"Falha na instalacao:\n{e}")
            btn.config(state="normal")

    btn = tk.Button(root, text="Instalar", width=20,
                    command=lambda: threading.Thread(target=_run, daemon=True).start())
    btn.pack(pady=4)
    root.mainloop()

if __name__ == "__main__":
    main()
