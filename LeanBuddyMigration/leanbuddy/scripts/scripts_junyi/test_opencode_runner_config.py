#!/usr/bin/env python3

from __future__ import annotations

import os
import signal
import subprocess
import sys
import tempfile
import time
import unittest
from pathlib import Path

import opencode_runner_config as config


class RunnerLifecycleTest(unittest.TestCase):
    def test_run_identity_separates_account_environments(self) -> None:
        script = Path("/tmp/demo-runner.py")
        previous = os.environ.get("XDG_DATA_HOME")
        try:
            os.environ["XDG_DATA_HOME"] = "/tmp/account-a"
            first = config._run_identity(script, ["--model", "demo", "Lemma4"])
            os.environ["XDG_DATA_HOME"] = "/tmp/account-b"
            second = config._run_identity(script, ["--model", "demo", "Lemma4"])
        finally:
            if previous is None:
                os.environ.pop("XDG_DATA_HOME", None)
            else:
                os.environ["XDG_DATA_HOME"] = previous
        self.assertNotEqual(first, second)

    def test_run_identity_includes_runtime_limits(self) -> None:
        script = Path("/tmp/demo-runner.py")
        previous = os.environ.get("OPENCODE_MAX_RETRIES")
        try:
            os.environ["OPENCODE_MAX_RETRIES"] = "5"
            first = config._run_identity(script, ["Lemma4"])
            os.environ["OPENCODE_MAX_RETRIES"] = "20"
            second = config._run_identity(script, ["Lemma4"])
        finally:
            if previous is None:
                os.environ.pop("OPENCODE_MAX_RETRIES", None)
            else:
                os.environ["OPENCODE_MAX_RETRIES"] = previous
        self.assertNotEqual(first, second)

    def test_identical_run_lock_is_exclusive_and_recoverable(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            lock = Path(temporary) / "run.lock"
            first = config._acquire_run_lock(lock)
            self.assertIsNotNone(first)
            try:
                self.assertIsNone(config._acquire_run_lock(lock))
            finally:
                if first is not None:
                    os.close(first)

            recovered = config._acquire_run_lock(lock)
            self.assertIsNotNone(recovered)
            if recovered is not None:
                os.close(recovered)

    def test_state_update_does_not_overwrite_a_newer_run(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            state = Path(temporary) / "run.json"
            config._write_state(state, {"run_id": "new", "status": "running"})
            config._update_state(state, "old", status="failed")
            self.assertEqual(config._read_state(state)["status"], "running")

    def test_terminal_state_cannot_be_resurrected_by_a_late_heartbeat(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            state = Path(temporary) / "run.json"
            config._write_state(state, {"run_id": "same", "status": "finished"})
            config._update_state(state, "same", status="running", heartbeat_at="late")
            self.assertEqual(config._read_state(state)["status"], "finished")

    def test_terminal_state_update_is_atomic_across_processes(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            state = root / "run.json"
            config._write_state(state, {"run_id": "same", "status": "running"})
            update_lock = config._state_update_lock_path(state)
            lock_fd = os.open(update_lock, os.O_CREAT | os.O_RDWR, 0o600)
            helper = (
                "from pathlib import Path; "
                "import sys; "
                f"sys.path.insert(0, {str(Path(__file__).resolve().parent)!r}); "
                "import opencode_runner_config as c; "
                "c._update_state(Path(sys.argv[1]), 'same', status='running', heartbeat_at='late')"
            )
            try:
                import fcntl

                fcntl.flock(lock_fd, fcntl.LOCK_EX)
                late_writer = subprocess.Popen([sys.executable, "-c", helper, str(state)])
                time.sleep(0.1)
                self.assertIsNone(late_writer.poll())
                config._write_state(state, {"run_id": "same", "status": "finished"})
            finally:
                os.close(lock_fd)

            self.assertEqual(late_writer.wait(timeout=3), 0)
            self.assertEqual(config._read_state(state)["status"], "finished")

    def test_detached_child_holds_lock_and_records_completion(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            helper = root / "detached_helper.py"
            scripts = Path(__file__).resolve().parent
            helper.write_text(
                "\n".join(
                    [
                        "import sys",
                        "import time",
                        "from pathlib import Path",
                        f"sys.path.insert(0, {str(scripts)!r})",
                        "from opencode_runner_config import finish_nohup_state, maybe_nohup",
                        "root = Path(__file__).resolve().parent",
                        "if maybe_nohup(root, Path(__file__).resolve(), sys.argv[1:]):",
                        "    raise SystemExit(0)",
                        "time.sleep(float(sys.argv[1]))",
                        "finish_nohup_state(0)",
                    ]
                )
                + "\n",
                encoding="utf-8",
            )
            environment = os.environ.copy()
            environment.update(
                {
                    "OPENCODE_RUN_NOHUP": "1",
                    "OPENCODE_NOHUP_LOG_DIR": str(root / "logs"),
                    "OPENCODE_RUN_STATE_DIR": str(root / "states"),
                    "OPENCODE_RUN_HEARTBEAT_SECONDS": "1",
                }
            )
            command = [sys.executable, str(helper), "1.0"]

            launched = subprocess.run(command, env=environment, text=True, capture_output=True, check=True)
            self.assertIn("nohup enabled", launched.stdout)
            state_path = next((root / "states").glob("*.json"))

            duplicate = subprocess.run(command, env=environment, text=True, capture_output=True, check=True)
            self.assertIn("identical detached run is already active", duplicate.stdout)

            deadline = time.monotonic() + 5
            while time.monotonic() < deadline:
                state = config._read_state(state_path)
                if state.get("status") == "finished":
                    break
                time.sleep(0.05)
            self.assertEqual(config._read_state(state_path).get("status"), "finished")

            deadline = time.monotonic() + 3
            relaunched = None
            while time.monotonic() < deadline:
                candidate = subprocess.run(command, env=environment, text=True, capture_output=True, check=True)
                if "nohup enabled" in candidate.stdout:
                    relaunched = candidate
                    break
                time.sleep(0.05)
            self.assertIsNotNone(relaunched)

            deadline = time.monotonic() + 5
            while time.monotonic() < deadline:
                if config._read_state(state_path).get("status") == "finished":
                    break
                time.sleep(0.05)
            self.assertEqual(config._read_state(state_path).get("status"), "finished")

    def test_shell_supervisor_uses_persistent_lock_state_and_inherited_fd(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            marker = root / "lock-marker.txt"
            empty_config = root / "empty.env"
            empty_config.write_text("", encoding="utf-8")
            scripts = Path(__file__).resolve().parent
            helper = root / "supervisor.sh"
            helper.write_text(
                "\n".join(
                    [
                        "#!/usr/bin/env bash",
                        "set -euo pipefail",
                        f"PROJECT_ROOT={str(scripts.parent)!r}",
                        f"source {str(scripts / 'opencode_runner_config.sh')!r}",
                        "opencode_config_load",
                        'opencode_config_maybe_nohup "$0" "$@"',
                        "python3 -c 'import os,sys,time; from pathlib import Path; fd=int(os.environ[\"OPENCODE_RUN_LOCK_FD\"]); os.fstat(fd); Path(sys.argv[1]).write_text(\"fd_ok\", encoding=\"utf-8\"); time.sleep(float(sys.argv[2]))' \"$1\" \"$2\"",
                    ]
                )
                + "\n",
                encoding="utf-8",
            )
            helper.chmod(0o755)
            environment = os.environ.copy()
            environment.update(
                {
                    "OPENCODE_RUN_CONFIG": str(empty_config),
                    "OPENCODE_RUN_NOHUP": "1",
                    "OPENCODE_RESULTS_ROOT": str(root / "results"),
                    "OPENCODE_NOHUP_LOG_DIR": str(root / "logs"),
                    "OPENCODE_RUN_STATE_DIR": str(root / "states"),
                    "OPENCODE_RUN_HEARTBEAT_SECONDS": "1",
                }
            )
            command = ["bash", str(helper), str(marker), "1.0"]

            launched = subprocess.run(command, env=environment, text=True, capture_output=True, check=True)
            self.assertIn("nohup enabled", launched.stdout)
            state_path = next((root / "states").glob("*.json"))

            deadline = time.monotonic() + 3
            while time.monotonic() < deadline and not marker.exists():
                time.sleep(0.05)
            self.assertEqual(marker.read_text(encoding="utf-8"), "fd_ok")

            duplicate = subprocess.run(command, env=environment, text=True, capture_output=True, check=True)
            self.assertIn("identical detached run is already active", duplicate.stdout)

            deadline = time.monotonic() + 5
            while time.monotonic() < deadline:
                if config._read_state(state_path).get("status") == "finished":
                    break
                time.sleep(0.05)
            state = config._read_state(state_path)
            self.assertEqual(state.get("status"), "finished")
            self.assertIsInstance(state.get("command_pid"), int)

    def test_lock_survives_abrupt_lifecycle_wrapper_death(self) -> None:
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            marker = root / "lock-marker.txt"
            empty_config = root / "empty.env"
            empty_config.write_text("", encoding="utf-8")
            scripts = Path(__file__).resolve().parent
            helper = root / "supervisor.sh"
            helper.write_text(
                "\n".join(
                    [
                        "#!/usr/bin/env bash",
                        "set -euo pipefail",
                        f"PROJECT_ROOT={str(scripts.parent)!r}",
                        f"source {str(scripts / 'opencode_runner_config.sh')!r}",
                        "opencode_config_load",
                        'opencode_config_maybe_nohup "$0" "$@"',
                        "python3 -c 'import os,sys,time; from pathlib import Path; os.fstat(int(os.environ[\"OPENCODE_RUN_LOCK_FD\"])); Path(sys.argv[1]).write_text(\"fd_ok\", encoding=\"utf-8\"); time.sleep(float(sys.argv[2]))' \"$1\" \"$2\"",
                    ]
                )
                + "\n",
                encoding="utf-8",
            )
            helper.chmod(0o755)
            environment = os.environ.copy()
            environment.update(
                {
                    "OPENCODE_RUN_CONFIG": str(empty_config),
                    "OPENCODE_RUN_NOHUP": "1",
                    "OPENCODE_RESULTS_ROOT": str(root / "results"),
                    "OPENCODE_NOHUP_LOG_DIR": str(root / "logs"),
                    "OPENCODE_RUN_STATE_DIR": str(root / "states"),
                    "OPENCODE_RUN_HEARTBEAT_SECONDS": "1",
                }
            )
            command = ["bash", str(helper), str(marker), "10.0"]
            launched = subprocess.run(command, env=environment, text=True, capture_output=True, check=True)
            self.assertIn("nohup enabled", launched.stdout)
            state_path = next((root / "states").glob("*.json"))

            deadline = time.monotonic() + 3
            state: dict = {}
            while time.monotonic() < deadline:
                state = config._read_state(state_path)
                if marker.exists() and isinstance(state.get("command_pid"), int):
                    break
                time.sleep(0.05)
            wrapper_pid = int(state["pid"])
            command_pid = int(state["command_pid"])
            try:
                os.kill(wrapper_pid, signal.SIGKILL)
                time.sleep(0.1)
                duplicate = subprocess.run(command, env=environment, text=True, capture_output=True, check=True)
                self.assertIn("identical detached run is already active", duplicate.stdout)
            finally:
                try:
                    os.killpg(command_pid, signal.SIGTERM)
                except ProcessLookupError:
                    pass

            lock_path = Path(state["lock"])
            deadline = time.monotonic() + 5
            recovered = None
            while time.monotonic() < deadline:
                recovered = config._acquire_run_lock(lock_path)
                if recovered is not None:
                    break
                time.sleep(0.05)
            self.assertIsNotNone(recovered)
            if recovered is not None:
                os.close(recovered)


if __name__ == "__main__":
    unittest.main()
