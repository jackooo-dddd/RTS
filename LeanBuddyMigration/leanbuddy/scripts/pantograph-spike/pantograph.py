"""Minimal Pantograph REPL client used by the Phase 1 spike (not part of the app).

The REPL is started as `lake env <repl> <modules…>` in a Lake project directory, prints `ready.`, then answers one
JSON line per command line (`<command> <json>`).
"""
import json
import os
import subprocess
import threading
import time


class Pantograph:
    def __init__(self, repl, project, modules, options=()):
        self.cmd = ["lake", "env", repl, *modules, *options]
        self.project = project
        t0 = time.time()
        self.proc = subprocess.Popen(
            self.cmd, cwd=project, stdin=subprocess.PIPE, stdout=subprocess.PIPE, stderr=subprocess.PIPE, text=True,
            bufsize=1,
        )
        line = self.proc.stdout.readline()
        if line.strip() != "ready.":
            err = self.proc.stderr.read()
            raise RuntimeError(f"pantograph did not start: {line!r} {err[:2000]}")
        self.startup_seconds = time.time() - t0

    def send(self, command, payload, timeout=600):
        line = f"{command} {json.dumps(payload, ensure_ascii=False)}\n"
        self.proc.stdin.write(line)
        self.proc.stdin.flush()
        out = {}

        def read():
            out["line"] = self.proc.stdout.readline()

        th = threading.Thread(target=read, daemon=True)
        th.start()
        th.join(timeout)
        if th.is_alive():
            self.kill()
            return {"error": "wallclock", "desc": f"no reply within {timeout}s"}
        raw = out["line"]
        if not raw:
            return {"error": "eof", "desc": self.proc.stderr.read()[:2000]}
        if raw.startswith("Error:"):
            return {"error": "malformed", "desc": raw.strip()}
        return json.loads(raw)

    def rss_mb(self):
        """Resident memory of the REPL process (the child of `lake env`)."""
        try:
            kids = subprocess.run(["pgrep", "-P", str(self.proc.pid)], capture_output=True, text=True).stdout.split()
            pids = kids or [str(self.proc.pid)]
            rss = subprocess.run(["ps", "-o", "rss=", "-p", ",".join(pids)], capture_output=True, text=True).stdout
            return sum(int(x) for x in rss.split()) / 1024
        except Exception:
            return None

    def kill(self):
        try:
            for pid in subprocess.run(["pgrep", "-P", str(self.proc.pid)], capture_output=True, text=True).stdout.split():
                os.kill(int(pid), 9)
            self.proc.kill()
        except Exception:
            pass

    def close(self):
        try:
            self.proc.stdin.write("\n")
            self.proc.stdin.flush()
            self.proc.wait(10)
        except Exception:
            self.kill()


def split_header(source):
    """Split a Lean file into (import lines, body). The header is the leading block of blank lines, comments and
    `import` commands; the body starts at the first other command. Returns (modules, header_text, body_text)."""
    lines = source.split("\n")
    modules, i, depth = [], 0, 0
    while i < len(lines):
        s = lines[i].strip()
        if depth:
            depth += s.count("/-") - s.count("-/")
            i += 1
            continue
        if s.startswith("/-"):
            depth = s.count("/-") - s.count("-/")
            i += 1
            continue
        if s == "" or s.startswith("--"):
            i += 1
            continue
        if s.startswith("import "):
            modules += s[len("import "):].split()
            i += 1
            continue
        break
    header = "\n".join(lines[:i])
    body = "\n".join(lines[i:])
    return modules, header, body
