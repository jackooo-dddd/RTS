from __future__ import annotations

import fcntl
import hashlib
import json
import os
import shlex
import signal
import subprocess
import sys
import threading
from datetime import datetime, timezone
from pathlib import Path

TRUE_VALUES = {"1", "true", "yes", "on"}
TERMINAL_RUN_STATUSES = {"finished", "failed", "error", "interrupted", "launch_failed"}
_NOHUP_STATE_PATH: Path | None = None
_NOHUP_RUN_ID: str | None = None
_NOHUP_HEARTBEAT_STOP = threading.Event()
_NOHUP_STATE_LOCK = threading.Lock()


def _config_path(root: Path) -> Path:
    override = os.environ.get("OPENCODE_RUN_CONFIG")
    if override:
        return Path(override).expanduser()
    default_config = root / "scripts" / "opencode_runner_config.env"
    if default_config.is_file():
        return default_config
    return root / "scripts" / "config.env"


def _parse_config_line(line: str) -> tuple[str, str] | None:
    stripped = line.strip()
    if not stripped or stripped.startswith("#"):
        return None
    if stripped.startswith("export "):
        stripped = stripped[len("export ") :].strip()
    key, separator, raw_value = stripped.partition("=")
    if not separator:
        return None
    key = key.strip()
    if not key or not key.replace("_", "A").isalnum() or key[0].isdigit():
        return None
    parts = shlex.split(raw_value, comments=True, posix=True)
    value = parts[0] if parts else ""
    return key, value


def load_runner_config(root: Path) -> None:
    config_file = _config_path(root)
    if config_file.is_file():
        for line in config_file.read_text(encoding="utf-8").splitlines():
            parsed = _parse_config_line(line)
            if parsed is None:
                continue
            key, value = parsed
            os.environ.setdefault(key, value)

            os.environ.setdefault("OPENCODE_RUN_CONFIG_RESOLVED", str(config_file))

    os.environ.setdefault("OPENCODE_RUN_NOHUP", "0")
    os.environ.setdefault("OPENCODE_ENABLE_SKILL", "0")
    os.environ.setdefault("OPENCODE_WITH_PAPER", "1")
    os.environ.setdefault("OPENCODE_FULL_PROSA", "0")
    os.environ.setdefault("OPENCODE_RESULTS_ROOT", str(root / "results"))
    os.environ.setdefault("OPENCODE_NOHUP_LOG_DIR", str(Path(os.environ["OPENCODE_RESULTS_ROOT"]) / "nohup"))
    os.environ.setdefault("OPENCODE_RUN_STATE_DIR", str(Path(os.environ["OPENCODE_NOHUP_LOG_DIR"]) / ".runs"))
    os.environ.setdefault("OPENCODE_RUN_HEARTBEAT_SECONDS", "30")
    os.environ.setdefault("OPENCODE_MIN_PROSA_SOURCE_DIR", "/home/junyi/prosabuddy/prosaworkspace")
    os.environ.setdefault("OPENCODE_FULL_PROSA_SOURCE_DIR", "/home/junyi/prosabuddy/prosaworkspace")
    os.environ.setdefault("OPENCODE_DIRECT_PROSABUDDY", "1")
    os.environ.setdefault("OPENCODE_CONFIG_DIR", "/home/junyi/prosabuddy/.opencode")
    if not config_bool("OPENCODE_DIRECT_PROSABUDDY"):
        os.environ.setdefault("OPENCODE_MODEL", "github-copilot/gpt-5.4")
    os.environ.setdefault("OPENCODE_OUR_DIRECT_PROSA_PROBE", "1")
    os.environ.setdefault("OPENCODE_OUR_DIRECT_PROSA_AGENT", "whole-lemma")
    os.environ.setdefault("OPENCODE_OUR_DIRECT_PROSA_PROBE_STEPS", "50")
    os.environ.setdefault("OPENCODE_OUR_DIRECT_PROSA_PROBE_TIMEOUT_SECONDS", "1800")


def config_bool(name: str, default: bool = False) -> bool:
    value = os.environ.get(name)
    if value is None:
        return default
    return value.strip().lower() in TRUE_VALUES


def should_skip_nohup(argv: list[str]) -> bool:
    return any(arg in {"-h", "--help", "--check", "--dry-run", "--list-accounts"} for arg in argv)


def _utc_now() -> str:
    return datetime.now(timezone.utc).isoformat()


def _positive_seconds(name: str, default: int) -> int:
    raw = os.environ.get(name, "").strip()
    try:
        value = int(raw)
    except ValueError:
        return default
    return value if value > 0 else default


def _run_identity(script_path: Path, argv: list[str]) -> str:
    identity_env = {
        key: os.environ.get(key, "")
        for key in (
            "XDG_DATA_HOME",
            "XDG_CONFIG_HOME",
            "XDG_STATE_HOME",
            "XDG_CACHE_HOME",
            "OPENCODE_MODEL",
            "OPENCODE_VARIANT",
            "OPENCODE_RESULT_PREFIX",
            "OPENCODE_OUTPUT_DIR",
            "OPENCODE_RUN_CONFIG_RESOLVED",
            "OPENCODE_MAX_TOTAL_TOKENS",
            "OPENCODE_MAX_RETRIES",
            "OPENCODE_RUN_TIMEOUT_SECONDS",
            "OPENCODE_MODEL_RESPONSE_TIMEOUT_SECONDS",
            "OPENCODE_CASESTUDY_DIR",
            "OPENCODE_FULL_PROSA_SOURCE_DIR",
            "OPENCODE_PROOF_WORKFLOW_MODE",
            "OPENCODE_CONFIG_CONTENT",
            "OPENAI_BASE_URL",
            "OPENAI_API_BASE",
        )
    }
    payload = json.dumps(
        {
            "script": str(script_path.resolve()),
            "argv": argv,
            "cwd": str(Path.cwd().resolve()),
            "environment": identity_env,
        },
        sort_keys=True,
        separators=(",", ":"),
    )
    return hashlib.sha256(payload.encode("utf-8")).hexdigest()[:20]


def _read_state(path: Path) -> dict:
    try:
        payload = json.loads(path.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError):
        return {}
    return payload if isinstance(payload, dict) else {}


def _write_state(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    temporary = path.with_name(f".{path.name}.{os.getpid()}.tmp")
    temporary.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    os.replace(temporary, path)


def _state_update_lock_path(path: Path) -> Path:
    return path.with_name(f".{path.name}.update.lock")


def _update_state(path: Path, run_id: str, **updates: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with _NOHUP_STATE_LOCK:
        update_lock_fd = os.open(_state_update_lock_path(path), os.O_CREAT | os.O_RDWR, 0o600)
        try:
            # Launcher, lifecycle wrapper, and heartbeat are separate processes.
            # Serialize the complete read-modify-write sequence across them so a
            # stale writer cannot race with and overwrite a terminal transition.
            fcntl.flock(update_lock_fd, fcntl.LOCK_EX)
            state = _read_state(path)
            if state.get("run_id") not in {None, run_id}:
                return
            # State transitions are monotonic. A late launcher update or heartbeat
            # must never resurrect a run after the child recorded a terminal state.
            if state.get("status") in TERMINAL_RUN_STATUSES:
                return
            state.update(updates)
            state["run_id"] = run_id
            _write_state(path, state)
        finally:
            os.close(update_lock_fd)


def _acquire_run_lock(path: Path) -> int | None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd = os.open(path, os.O_CREAT | os.O_RDWR, 0o600)
    try:
        fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        os.close(fd)
        return None
    return fd


def inherited_run_lock_fds() -> tuple[int, ...]:
    """Return the live lifecycle lock inherited from a supervisor, if any."""
    raw = os.environ.get("OPENCODE_RUN_LOCK_FD", "").strip()
    if not raw:
        return ()
    try:
        fd = int(raw)
        if fd < 0:
            return ()
        os.fstat(fd)
    except (OSError, ValueError):
        return ()
    return (fd,)


def _start_nohup_child_state() -> None:
    global _NOHUP_STATE_PATH, _NOHUP_RUN_ID
    raw_path = os.environ.get("OPENCODE_NOHUP_STATE_PATH")
    run_id = os.environ.get("OPENCODE_NOHUP_RUN_ID")
    if not raw_path or not run_id:
        return
    _NOHUP_STATE_PATH = Path(raw_path)
    _NOHUP_RUN_ID = run_id
    _NOHUP_HEARTBEAT_STOP.clear()
    _update_state(
        _NOHUP_STATE_PATH,
        run_id,
        status="running",
        pid=os.getpid(),
        heartbeat_at=_utc_now(),
    )

    interval = _positive_seconds("OPENCODE_RUN_HEARTBEAT_SECONDS", 30)

    def heartbeat() -> None:
        while not _NOHUP_HEARTBEAT_STOP.wait(interval):
            if _NOHUP_STATE_PATH is None or _NOHUP_RUN_ID is None:
                return
            _update_state(
                _NOHUP_STATE_PATH,
                _NOHUP_RUN_ID,
                status="running",
                pid=os.getpid(),
                heartbeat_at=_utc_now(),
            )

    threading.Thread(target=heartbeat, name="opencode-run-heartbeat", daemon=True).start()


def finish_nohup_state(exit_code: int, *, status: str | None = None) -> None:
    _NOHUP_HEARTBEAT_STOP.set()
    if _NOHUP_STATE_PATH is None or _NOHUP_RUN_ID is None:
        return
    _update_state(
        _NOHUP_STATE_PATH,
        _NOHUP_RUN_ID,
        status=status or ("finished" if exit_code == 0 else "failed"),
        pid=os.getpid(),
        exit_code=exit_code,
        heartbeat_at=_utc_now(),
        finished_at=_utc_now(),
    )


def maybe_nohup(root: Path, script_path: Path, argv: list[str]) -> bool:
    if not config_bool("OPENCODE_RUN_NOHUP"):
        return False
    if os.environ.get("OPENCODE_NOHUP_CHILD") == "1":
        _start_nohup_child_state()
        return False
    if should_skip_nohup(argv):
        return False

    log_dir = Path(
        os.environ.get(
            "OPENCODE_NOHUP_LOG_DIR",
            str(Path(os.environ.get("OPENCODE_RESULTS_ROOT", str(root / "results"))) / "nohup"),
        )
    ).expanduser()
    log_dir.mkdir(parents=True, exist_ok=True)
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
    log_path = Path(os.environ.get("OPENCODE_NOHUP_LOG", str(log_dir / f"{script_path.stem}_{stamp}.log"))).expanduser()
    log_path.parent.mkdir(parents=True, exist_ok=True)

    identity = _run_identity(script_path, argv)
    state_dir = Path(os.environ.get("OPENCODE_RUN_STATE_DIR", str(log_dir / ".runs"))).expanduser()
    state_dir.mkdir(parents=True, exist_ok=True)
    lock_path = state_dir / f"{script_path.stem}-{identity}.lock"
    state_path = state_dir / f"{script_path.stem}-{identity}.json"
    lock_fd = _acquire_run_lock(lock_path)
    if lock_fd is None:
        state = _read_state(state_path)
        print("identical detached run is already active")
        if state.get("pid") is not None:
            print(f"pid: {state['pid']}")
        if state.get("heartbeat_at"):
            print(f"heartbeat: {state['heartbeat_at']}")
        print(f"state: {state_path}")
        if state.get("log"):
            print(f"log: {state['log']}")
        return True

    run_id = f"{stamp}-{os.getpid()}"
    command = [sys.executable, str(script_path), *argv]
    _write_state(
        state_path,
        {
            "run_id": run_id,
            "identity": identity,
            "status": "starting",
            "script": str(script_path.resolve()),
            "argv": argv,
            "command": command,
            "launcher_pid": os.getpid(),
            "started_at": _utc_now(),
            "heartbeat_at": _utc_now(),
            "log": str(log_path),
            "lock": str(lock_path),
        },
    )

    env = os.environ.copy()
    env["OPENCODE_NOHUP_CHILD"] = "1"
    env["OPENCODE_NOHUP_RUN_ID"] = run_id
    env["OPENCODE_NOHUP_STATE_PATH"] = str(state_path)
    env["OPENCODE_RUN_LOCK_FD"] = str(lock_fd)
    try:
        with log_path.open("ab") as log_file:
            proc = subprocess.Popen(
                command,
                stdin=subprocess.DEVNULL,
                stdout=log_file,
                stderr=subprocess.STDOUT,
                env=env,
                start_new_session=True,
                pass_fds=(lock_fd,),
            )
    except Exception:
        _update_state(
            state_path,
            run_id,
            status="launch_failed",
            heartbeat_at=_utc_now(),
            finished_at=_utc_now(),
        )
        os.close(lock_fd)
        raise
    os.close(lock_fd)
    _update_state(
        state_path,
        run_id,
        status="running",
        pid=proc.pid,
        heartbeat_at=_utc_now(),
    )
    print("nohup enabled by OPENCODE_RUN_NOHUP=1")
    print(f"log: {log_path}")
    print(f"pid: {proc.pid}")
    print(f"state: {state_path}")
    return True


def _terminate_managed_process(proc: subprocess.Popen[bytes], *, grace_seconds: float = 10) -> None:
    if proc.poll() is not None:
        return
    try:
        os.killpg(proc.pid, signal.SIGTERM)
    except ProcessLookupError:
        return
    try:
        proc.wait(timeout=grace_seconds)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        try:
            proc.wait(timeout=5)
        except subprocess.TimeoutExpired:
            pass


def _managed_child(command: list[str]) -> int:
    """Run a shell supervisor while retaining heartbeat and the lifecycle lock."""
    _start_nohup_child_state()
    lock_fds = inherited_run_lock_fds()
    if not lock_fds:
        finish_nohup_state(1, status="error")
        raise RuntimeError("managed detached child did not inherit OPENCODE_RUN_LOCK_FD")

    env = os.environ.copy()
    env["OPENCODE_NOHUP_CHILD"] = "1"
    received_signal: int | None = None
    proc: subprocess.Popen[bytes] | None = None

    def handle_signal(signum: int, _frame: object) -> None:
        nonlocal received_signal
        received_signal = signum
        if proc is not None:
            try:
                os.killpg(proc.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass

    previous_handlers = {
        signum: signal.getsignal(signum)
        for signum in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP)
    }
    try:
        proc = subprocess.Popen(
            command,
            stdin=subprocess.DEVNULL,
            env=env,
            start_new_session=True,
            pass_fds=lock_fds,
        )
        if _NOHUP_STATE_PATH is not None and _NOHUP_RUN_ID is not None:
            _update_state(
                _NOHUP_STATE_PATH,
                _NOHUP_RUN_ID,
                status="running",
                pid=os.getpid(),
                command_pid=proc.pid,
                heartbeat_at=_utc_now(),
            )
        for signum in previous_handlers:
            signal.signal(signum, handle_signal)
        return_code = proc.wait()
    except BaseException:
        if proc is not None:
            _terminate_managed_process(proc)
        finish_nohup_state(1, status="error")
        raise
    finally:
        for signum, handler in previous_handlers.items():
            signal.signal(signum, handler)

    if received_signal is not None:
        exit_code = 128 + received_signal
        finish_nohup_state(exit_code, status="interrupted")
        return exit_code
    exit_code = return_code if return_code >= 0 else 128 + abs(return_code)
    finish_nohup_state(exit_code)
    return exit_code


def launch_shell_nohup(root: Path, script_path: Path, argv: list[str]) -> bool:
    """Detach a shell supervisor under the same lock/state protocol as Python runners."""
    log_dir = Path(
        os.environ.get(
            "OPENCODE_NOHUP_LOG_DIR",
            str(Path(os.environ.get("OPENCODE_RESULTS_ROOT", str(root / "results"))) / "nohup"),
        )
    ).expanduser()
    log_dir.mkdir(parents=True, exist_ok=True)
    stamp = datetime.now().strftime("%Y%m%d_%H%M%S_%f")
    log_path = Path(
        os.environ.get("OPENCODE_NOHUP_LOG", str(log_dir / f"{script_path.stem}_{stamp}.log"))
    ).expanduser()
    log_path.parent.mkdir(parents=True, exist_ok=True)

    identity = _run_identity(script_path, argv)
    state_dir = Path(os.environ.get("OPENCODE_RUN_STATE_DIR", str(log_dir / ".runs"))).expanduser()
    state_dir.mkdir(parents=True, exist_ok=True)
    lock_path = state_dir / f"{script_path.stem}-{identity}.lock"
    state_path = state_dir / f"{script_path.stem}-{identity}.json"
    lock_fd = _acquire_run_lock(lock_path)
    if lock_fd is None:
        state = _read_state(state_path)
        print("identical detached run is already active")
        if state.get("pid") is not None:
            print(f"pid: {state['pid']}")
        if state.get("command_pid") is not None:
            print(f"command_pid: {state['command_pid']}")
        if state.get("heartbeat_at"):
            print(f"heartbeat: {state['heartbeat_at']}")
        print(f"state: {state_path}")
        if state.get("log"):
            print(f"log: {state['log']}")
        return True

    run_id = f"{stamp}-{os.getpid()}"
    command = ["/bin/bash", str(script_path), *argv]
    wrapper_command = [
        sys.executable,
        str(Path(__file__).resolve()),
        "managed-child",
        *command,
    ]
    _write_state(
        state_path,
        {
            "run_id": run_id,
            "identity": identity,
            "status": "starting",
            "script": str(script_path.resolve()),
            "argv": argv,
            "command": command,
            "launcher_pid": os.getpid(),
            "started_at": _utc_now(),
            "heartbeat_at": _utc_now(),
            "log": str(log_path),
            "lock": str(lock_path),
        },
    )

    env = os.environ.copy()
    env["OPENCODE_NOHUP_CHILD"] = "1"
    env["OPENCODE_NOHUP_RUN_ID"] = run_id
    env["OPENCODE_NOHUP_STATE_PATH"] = str(state_path)
    env["OPENCODE_RUN_LOCK_FD"] = str(lock_fd)
    try:
        with log_path.open("ab") as log_file:
            proc = subprocess.Popen(
                wrapper_command,
                stdin=subprocess.DEVNULL,
                stdout=log_file,
                stderr=subprocess.STDOUT,
                env=env,
                start_new_session=True,
                pass_fds=(lock_fd,),
            )
    except Exception:
        _update_state(
            state_path,
            run_id,
            status="launch_failed",
            heartbeat_at=_utc_now(),
            finished_at=_utc_now(),
        )
        os.close(lock_fd)
        raise
    os.close(lock_fd)
    _update_state(
        state_path,
        run_id,
        status="running",
        pid=proc.pid,
        heartbeat_at=_utc_now(),
    )
    print("nohup enabled by OPENCODE_RUN_NOHUP=1")
    print(f"log: {log_path}")
    print(f"pid: {proc.pid}")
    print(f"state: {state_path}")
    return True


def _cli(argv: list[str]) -> int:
    if not argv:
        print("usage: opencode_runner_config.py detach-shell ROOT SCRIPT [ARGS...]", file=sys.stderr)
        return 2
    command = argv[0]
    if command == "detach-shell":
        if len(argv) < 3:
            print("detach-shell requires ROOT and SCRIPT", file=sys.stderr)
            return 2
        launch_shell_nohup(Path(argv[1]), Path(argv[2]), argv[3:])
        return 0
    if command == "managed-child":
        if len(argv) < 2:
            print("managed-child requires a command", file=sys.stderr)
            return 2
        return _managed_child(argv[1:])
    print(f"unknown command: {command}", file=sys.stderr)
    return 2


if __name__ == "__main__":
    raise SystemExit(_cli(sys.argv[1:]))
