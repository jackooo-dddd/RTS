#!/usr/bin/env python3
"""
Serial runner for OpenCode minimal-Prosa casestudy theorem proving.

Matches scripts/run_prosa_opencode_minprosa.py in structure, but operates on
casestudy workspaces from datasets_v06/casestudy_v06 instead of benchmark
theorem files.

Workspace IDs are the casestudy directory names, e.g.:
  2009-RTSS-Lemma3
  2007-RTSS-Theorem1

For each requested casestudy:
    1) Stage a fresh runtime workspace containing only the target theorem file and
            its transitive Prosa dependencies, or the full Prosa tree when requested.
  2) Write a per-workspace opencode.jsonc config that allows only compilation of
      the staged theorem file.
  3) Invoke `opencode run` with a prompt that forbids cheating, keeps the agent
      inside the staged workspace, and requires it to continue until `coqc`
      succeeds.
  4) Re-check compilation after each agent exit; if compilation still fails,
      resume until the configured retry, time, or summed-token limit.

Environment variables consumed by this script:
  XDG_DATA_HOME  – override to isolate opencode auth/session data per account.
    OPENCODE_BIN   – path to the opencode binary/wrapper (default: scripts/opencode_trace_local.sh).
    OPENCODE_RESULT_PREFIX  – result directory prefix written under results/.
    OPENCODE_RECORD_RUNNER  – metadata label stored in results/*/config.json.
"""

from __future__ import annotations

import json
import os
import queue
import re
import runpy
import signal
import shutil
import sqlite3
import subprocess
import sys
import threading
import time
import hashlib
from datetime import datetime, timezone
from functools import lru_cache
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "scripts"))
_CONFIG_HELPER = runpy.run_path(str(ROOT / "scripts" / "opencode_runner_config.py"))
config_bool = _CONFIG_HELPER["config_bool"]
load_runner_config = _CONFIG_HELPER["load_runner_config"]
maybe_nohup = _CONFIG_HELPER["maybe_nohup"]
finish_nohup_state = _CONFIG_HELPER["finish_nohup_state"]
inherited_run_lock_fds = _CONFIG_HELPER["inherited_run_lock_fds"]

load_runner_config(ROOT)

RESULTS_ROOT = Path(os.environ.get("OPENCODE_RESULTS_ROOT", str(ROOT / "results"))).expanduser()
OPENCODE_PROMPT = ROOT / "scripts" / "opencode_prompt.md"
DEFAULT_OPENCODE_BIN = Path(
    os.environ.get("OPENCODE_BIN", str(ROOT / "scripts" / "opencode_trace_local.sh"))
)
DEFAULT_SKILL_SOURCE_DIR = Path(
    os.environ.get("OPENCODE_SKILL_SOURCE_DIR", str(ROOT / "opencode-trace" / ".opencode" / "skill"))
)
ENV_RESULT_PREFIX = os.environ.get("OPENCODE_RESULT_PREFIX")
DEFAULT_RECORD_RUNNER = os.environ.get(
    "OPENCODE_RECORD_RUNNER", "run_casestudy_opencode_minprosa.py"
)
_ACTIVE_OPENCODE_PROCESS: subprocess.Popen[bytes] | None = None


def _terminate_process_group(proc: subprocess.Popen[bytes], *, grace_seconds: float = 30) -> None:
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
            proc.wait(timeout=10)
        except subprocess.TimeoutExpired:
            pass


def _runner_signal_handler(signum: int, _frame: object) -> None:
    proc = _ACTIVE_OPENCODE_PROCESS
    if proc is not None:
        _terminate_process_group(proc, grace_seconds=5)
    raise SystemExit(128 + signum)


for _runner_signal in (signal.SIGINT, signal.SIGTERM, signal.SIGHUP):
    signal.signal(_runner_signal, _runner_signal_handler)

DEFAULT_CASESTUDY_ROOT = ROOT / "datasets_v06" / "casestudy_v06"
PROSA_SOURCE_ROOT = Path(
    os.environ.get("OPENCODE_MIN_PROSA_SOURCE_DIR", str(ROOT / "datasets_v06" / "prosa_v06_classic"))
)
FULL_PROSA_SOURCE_ROOT = Path(
    os.environ.get("OPENCODE_FULL_PROSA_SOURCE_DIR", str(ROOT / "prosa_v06"))
)

DECLARATION_KEYWORDS = "Theorem|Lemma|Corollary|Proposition|Fact|Remark|Example"
THEOREM_PATTERN = re.compile(
    rf"^(?:Local\s+)?({DECLARATION_KEYWORDS})\s+([A-Za-z0-9_\.]+)\b"
)
ADDITIVE_IMPORT_PATTERN = re.compile(
    r"^\s*(?:From\s+[A-Za-z0-9_'.]+(?:\s+[A-Za-z0-9_'.]+)*\s+)?Require\s+(?:Import|Export)\b.*\.\s*$"
)
PAPER_ARTIFACT_SUFFIXES = {".pdf", ".tex", ".jpg", ".jpeg", ".png"}
AUTOAGENT_RESERVATION_FILE = ".autoagent-reservation.json"
PROSA_LOGICAL_ROOTS = (
    "analysis",
    "behavior",
    "classic",
    "implementation",
    "model",
    "results",
    "util",
)

# ---------------------------------------------------------------------------
# Utilities
# ---------------------------------------------------------------------------


def now_iso() -> str:
    return datetime.now(timezone.utc).isoformat()


def normalize_tag_component(value: str) -> str:
    trimmed = value.rsplit("/", 1)[-1].strip().lower()
    normalized = re.sub(r"[^a-z0-9._-]+", "-", trimmed).strip("-")
    return normalized or "default"


def _split_model_ref(model: str | None) -> tuple[str | None, str | None]:
    if not model:
        return None, None
    provider_id, sep, model_id = model.partition("/")
    if not sep or not provider_id or not model_id:
        return None, None
    return provider_id, model_id


def _inject_openrouter_service_tier_config(
    env: dict[str, str],
    *,
    model: str | None,
    service_tier: str | None,
) -> tuple[bool, str | None]:
    target_model = "openrouter/google/gemini-3.1-flash-lite"
    tier = (service_tier or "").strip()
    if not tier:
        return False, None

    # Keep behavior unchanged for every other model.
    if model != target_model:
        return False, None

    provider_id, model_id = _split_model_ref(model)
    if provider_id != "openrouter" or not model_id:
        return False, f"OPENCODE_SERVICE_TIER is set but model is not openrouter/* (model={model!r})"

    existing_raw = (env.get("OPENCODE_CONFIG_CONTENT") or "").strip()
    payload: dict[str, object]
    if existing_raw:
        try:
            parsed = json.loads(existing_raw)
        except json.JSONDecodeError:
            return False, "OPENCODE_CONFIG_CONTENT is not valid JSON; cannot merge service tier override"
        if not isinstance(parsed, dict):
            return False, "OPENCODE_CONFIG_CONTENT must be a JSON object; cannot merge service tier override"
        payload = dict(parsed)
    else:
        payload = {}

    provider = payload.get("provider")
    if not isinstance(provider, dict):
        provider = {}
    openrouter_cfg = provider.get("openrouter")
    if not isinstance(openrouter_cfg, dict):
        openrouter_cfg = {}
    models = openrouter_cfg.get("models")
    if not isinstance(models, dict):
        models = {}
    model_cfg = models.get(model_id)
    if not isinstance(model_cfg, dict):
        model_cfg = {}
    options = model_cfg.get("options")
    if not isinstance(options, dict):
        options = {}

    body = options.get("body")
    if not isinstance(body, dict):
        body = {}

    # OpenRouter provider options can forward raw request-body fields via `body`.
    # Keep compatibility with older option shapes by setting both forms.
    body["service_tier"] = tier
    options["body"] = body
    options["service_tier"] = tier
    options["serviceTier"] = tier
    model_cfg["options"] = options
    models[model_id] = model_cfg
    openrouter_cfg["models"] = models
    provider["openrouter"] = openrouter_cfg
    payload["provider"] = provider

    env["OPENCODE_CONFIG_CONTENT"] = json.dumps(payload, ensure_ascii=False)
    return True, None


def build_experiment_tag(
    *,
    model: str | None,
    full_prosa: bool,
    enable_skill: bool,
) -> str:
    prosa_tag = "fullprosa" if full_prosa else "minprosa"
    model_tag = normalize_tag_component(model or "default")
    skill_tag = "withskill" if enable_skill else "noskill"
    return f"{prosa_tag}_{model_tag}_{skill_tag}"


def resolve_result_prefix(options: dict) -> tuple[str, str]:
    experiment_tag = build_experiment_tag(
        model=options.get("model"),
        full_prosa=bool(options.get("full_prosa")),
        enable_skill=bool(options.get("enable_skill")),
    )
    if ENV_RESULT_PREFIX:
        return ENV_RESULT_PREFIX, experiment_tag
    return f"opencode_casestudy_{experiment_tag}", experiment_tag


def write_text(path: Path, content: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(content, encoding="utf-8")


def write_json(path: Path, payload: object) -> None:
    write_text(path, json.dumps(payload, indent=2, ensure_ascii=False))


def append_jsonl(path: Path, payload: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("a", encoding="utf-8") as f:
        f.write(json.dumps(payload, ensure_ascii=False) + "\n")


def consume_output_dir_reservation(output_dir: Path) -> Path:
    """Validate and consume an output leaf preallocated by AutoAgent."""
    lexical = output_dir.expanduser().absolute()
    if lexical.is_symlink():
        raise RuntimeError(f"--output-dir itself cannot be a symlink: {lexical}")
    result = lexical.resolve()
    if not result.is_dir():
        raise RuntimeError(f"--output-dir must be an existing reserved directory: {result}")
    try:
        result.relative_to(ROOT.resolve())
    except ValueError:
        pass
    else:
        raise RuntimeError(f"--output-dir must be outside the experiment repository: {result}")
    marker = result / AUTOAGENT_RESERVATION_FILE
    entries = list(result.iterdir())
    if set(entries) != {marker} or marker.is_symlink() or not marker.is_file():
        raise RuntimeError(
            f"--output-dir must contain only {AUTOAGENT_RESERVATION_FILE}: {result}"
        )
    try:
        reservation = json.loads(marker.read_text(encoding="utf-8"))
    except (OSError, json.JSONDecodeError) as exc:
        raise RuntimeError(f"Invalid AutoAgent output reservation marker: {marker}") from exc
    if (
        not isinstance(reservation, dict)
        or reservation.get("schema_version") != 1
        or not isinstance(reservation.get("operation_id"), str)
        or not reservation["operation_id"]
    ):
        raise RuntimeError(f"Invalid AutoAgent output reservation payload: {marker}")
    marker.unlink()
    return result


def _initial_read_guidance(theorem_file: Path) -> str:
    return (
        f"Begin by reading `proof.tex` if it exists, then read `{theorem_file.name}`, "
        "then examine only the `prosa/` directory for directly relevant lemmas and definitions.\n"
    )


def _bridge_scope_text() -> str:
    return "the directly relevant facts in the target file and `prosa/`"


# ---------------------------------------------------------------------------
# Workspace helpers
# ---------------------------------------------------------------------------

from archived.extract_prosa_depend import copy_minimal_prosa_project  # noqa: E402


def available_workspaces() -> list[str]:
    return sorted(casestudy_workspace_map())


def resolve_cases_root(cases_dir: str | None = None) -> Path:
    if cases_dir:
        return Path(cases_dir).expanduser().resolve()
    env_override = os.environ.get("OPENCODE_CASESTUDY_DIR")
    if env_override:
        return Path(env_override).expanduser().resolve()
    return DEFAULT_CASESTUDY_ROOT


def is_casestudy_theorem_file(path: Path) -> bool:
    return (
        path.is_file()
        and path.suffix == ".v"
        and not path.name.startswith("agent_request")
        and not path.name.startswith("OpencodePrefix_")
        and not path.name.startswith("ProsabuddyToolchainPreflight")
        and not path.name.endswith("_cp_aux.v")
    )


@lru_cache(maxsize=1)
def casestudy_workspace_map(cases_root: Path | None = None) -> dict[str, Path]:
    mapping: dict[str, Path] = {}
    root = cases_root or resolve_cases_root()
    if not root.is_dir():
        return mapping
    for casestudy_dir in sorted(root.iterdir()):
        if not casestudy_dir.is_dir():
            continue
        workspace_name = casestudy_dir.name
        # Find the theorem .v file inside the casestudy directory
        candidates = sorted(
            p
            for p in casestudy_dir.glob("*.v")
            if is_casestudy_theorem_file(p)
        )
        if not candidates:
            continue
        mapping[workspace_name] = casestudy_dir
    return mapping


def resolve_workspace_source_dir(workspace_name: str, cases_root: Path | None = None) -> Path:
    try:
        return casestudy_workspace_map(cases_root)[workspace_name]
    except KeyError as exc:
        raise RuntimeError(f"Unknown casestudy workspace: {workspace_name}") from exc


def root_theorem_file(workspace: Path) -> Path:
    if workspace.is_file():
        return workspace
    candidates = sorted(
        p
        for p in workspace.glob("*.v")
        if is_casestudy_theorem_file(p)
    )
    if not candidates:
        raise RuntimeError(f"No root .v file found in {workspace}")
    return candidates[0]


def target_theorem_kind(v_file: Path) -> str:
    matches: list[tuple[str, str]] = []
    with v_file.open("r", encoding="utf-8", errors="ignore") as f:
        for line in f:
            m = THEOREM_PATTERN.match(line.strip())
            if m:
                matches.append((m.group(1).lower(), m.group(2)))
    if not matches:
        raise RuntimeError(f"No supported proof declarations found in {v_file}")
    return matches[-1][0]


def target_theorem_name(v_file: Path) -> str:
    matches: list[tuple[str, str]] = []
    with v_file.open("r", encoding="utf-8", errors="ignore") as f:
        for line in f:
            m = THEOREM_PATTERN.match(line.strip())
            if m:
                matches.append((m.group(1).lower(), m.group(2)))
    if not matches:
        raise RuntimeError(f"No supported proof declarations found in {v_file}")
    return matches[-1][1]


def _extract_target_theorem_ranges(
    content: str,
    theorem_kind: str,
    theorem_name: str,
    *,
    allow_unterminated: bool = False,
    theorem_suffix: str | None = None,
) -> tuple[int, int, int, int] | None:
    decl_pattern = re.compile(
        rf"^\s*(?:Local\s+)?{re.escape(theorem_kind)}\s+{re.escape(theorem_name)}\b",
        re.MULTILINE | re.IGNORECASE,
    )
    decl_match = decl_pattern.search(content)
    if decl_match is None:
        return None

    decl_start = decl_match.start()
    rest = content[decl_start:]
    proof_match = re.search(r"\bProof\b", rest)
    terminator_match = re.search(r"\b(Qed|Defined|Admitted)\s*\.", rest)
    if terminator_match is None:
        if not allow_unterminated or proof_match is None:
            return None

        body_start = decl_start + proof_match.start()
        statement_end = body_start
        if theorem_suffix:
            suffix_start = content.find(theorem_suffix, body_start)
            if suffix_start < 0:
                return None
            body_end = suffix_start
        else:
            body_end = len(content)
        return decl_start, statement_end, body_start, body_end

    terminator_start = decl_start + terminator_match.start()
    body_start = decl_start + proof_match.start() if proof_match else terminator_start
    body_end = decl_start + terminator_match.end()
    statement_end = body_start
    return decl_start, statement_end, body_start, body_end


def _unterminated_proof_message(theorem_name: str) -> str:
    return (
        f"Target theorem `{theorem_name}` is still present, but its proof body has no "
        "Qed/Defined/Admitted terminator. Continue from the current proof state, "
        "restore a well-formed theorem block, and finish the proof with Qed."
    )


def extract_target_theorem_statement(v_file: Path) -> str:
    content = v_file.read_text(encoding="utf-8", errors="ignore")
    theorem_kind = target_theorem_kind(v_file)
    theorem_name = target_theorem_name(v_file)
    ranges = _extract_target_theorem_ranges(content, theorem_kind, theorem_name)
    if ranges is None:
        raise RuntimeError(f"Could not locate target theorem statement in {v_file}")
    decl_start, statement_end, _body_start, _body_end = ranges
    return content[decl_start:statement_end].rstrip()


def _normalize_terminal_whitespace(text: str) -> str:
    return text.replace("\r\n", "\n").rstrip()


def _normalize_whitespace(text: str) -> str:
    """Collapse all whitespace runs (spaces, tabs, newlines) to a single space and strip ends."""
    return re.sub(r"\s+", " ", text).strip()


def _is_allowed_prefix_addition(line: str) -> bool:
    stripped = line.strip()
    return not stripped or bool(ADDITIVE_IMPORT_PATTERN.fullmatch(line.rstrip("\r\n")))


def _extract_allowed_prefix_additions(source_prefix: str, current_prefix: str) -> tuple[bool, list[str]]:
    source_lines = source_prefix.splitlines(keepends=True)
    current_lines = current_prefix.splitlines(keepends=True)
    source_index = 0
    current_index = 0
    added_lines: list[str] = []

    while source_index < len(source_lines) and current_index < len(current_lines):
        if current_lines[current_index] == source_lines[source_index]:
            source_index += 1
            current_index += 1
            continue

        if _is_allowed_prefix_addition(current_lines[current_index]):
            added_lines.append(current_lines[current_index].rstrip("\r\n"))
            current_index += 1
            continue

        return False, []

    if source_index != len(source_lines):
        return False, []

    while current_index < len(current_lines):
        if not _is_allowed_prefix_addition(current_lines[current_index]):
            return False, []
        added_lines.append(current_lines[current_index].rstrip("\r\n"))
        current_index += 1

    return True, [line for line in added_lines if line.strip()]


def inspect_theorem_edit_integrity(source_theorem_file: Path, theorem_file: Path) -> dict:
    info: dict = {}
    theorem_kind = target_theorem_kind(source_theorem_file)
    theorem_name = target_theorem_name(source_theorem_file)

    source_text = source_theorem_file.read_text(encoding="utf-8", errors="ignore")
    current_text = theorem_file.read_text(encoding="utf-8", errors="ignore")

    source_ranges = _extract_target_theorem_ranges(source_text, theorem_kind, theorem_name)
    source_suffix = ""
    if source_ranges is not None:
        source_suffix = source_text[source_ranges[3]:]

    current_ranges = _extract_target_theorem_ranges(current_text, theorem_kind, theorem_name)
    if current_ranges is None and source_suffix:
        current_ranges = _extract_target_theorem_ranges(
            current_text,
            theorem_kind,
            theorem_name,
            allow_unterminated=True,
            theorem_suffix=source_suffix,
        )
        if current_ranges is not None:
            info["target_proof_unterminated"] = True
            info["compile_error"] = _unterminated_proof_message(theorem_name)

    if source_ranges is None:
        info["integrity_check_failed"] = True
        info["proof_verified"] = False
        info["compile_error"] = (
            f"Runner error: could not locate the target theorem `{theorem_name}` in the source file."
        )
        return info

    if current_ranges is None:
        info["unauthorized_modification"] = True
        info["theorem_statement_changed"] = True
        info["proof_verified"] = False
        info["compile_error"] = (
            "Unauthorized file modification: the target theorem declaration was renamed, removed, "
            "or could no longer be parsed. Only the original proof body may be edited."
        )
        return info

    source_decl_start, source_statement_end, source_body_start, source_body_end = source_ranges
    current_decl_start, current_statement_end, current_body_start, current_body_end = current_ranges

    source_prefix = source_text[:source_decl_start]
    current_prefix = current_text[:current_decl_start]
    source_statement = source_text[source_decl_start:source_statement_end]
    current_statement = current_text[current_decl_start:current_statement_end]
    source_suffix = source_text[source_body_end:]
    current_suffix = current_text[current_body_end:]

    issues: list[str] = []
    prefix_ok, allowed_prefix_additions = _extract_allowed_prefix_additions(source_prefix, current_prefix)
    if not prefix_ok:
        issues.append("text before the target theorem changed")
    elif allowed_prefix_additions:
        info["allowed_import_additions"] = allowed_prefix_additions
        info["allowed_outside_proof_edit"] = True
    if _normalize_whitespace(current_statement) != _normalize_whitespace(source_statement):
        issues.append("the target theorem declaration or statement changed")
        info["theorem_statement_changed"] = True
    if _normalize_whitespace(_normalize_terminal_whitespace(current_suffix)) != _normalize_whitespace(_normalize_terminal_whitespace(source_suffix)):
        issues.append("text after the target proof block changed")

    info["proof_body_only_edit"] = not issues and not allowed_prefix_additions
    if issues:
        info["unauthorized_modification"] = True
        info["integrity_issues"] = issues
        info["proof_verified"] = False
        info["compile_error"] = (
            "Unauthorized file modification: only the original proof body of the target theorem may be edited. "
            + "; ".join(issues)
            + "."
        )

    return info


def copy_full_prosa_project(source_root: Path, destination: Path) -> None:
    source_root = source_root.expanduser().resolve()
    if not source_root.is_dir():
        raise RuntimeError(f"Missing full Prosa source root: {source_root}")

    if destination.exists() or destination.is_symlink():
        if destination.is_dir() and not destination.is_symlink():
            shutil.rmtree(destination)
        else:
            destination.unlink()

    logical_roots = [source_root / name for name in PROSA_LOGICAL_ROOTS]
    if all(path.is_dir() for path in logical_roots):
        destination.mkdir(parents=True)
        for source in logical_roots:
            shutil.copytree(source, destination / source.name, symlinks=False)
    else:
        # Keep supporting generic full-Prosa fixtures and older layouts while
        # ensuring result artifacts never retain source-tree symlinks.
        shutil.copytree(source_root, destination, symlinks=False)

    symlinks = [path for path in destination.rglob("*") if path.is_symlink()]
    if symlinks:
        raise RuntimeError(f"Full Prosa staging retained a symlink: {symlinks[0]}")


def write_workspace_coq_project(workspace_dir: Path) -> None:
    """Publish the same deterministic Prosa mapping used by editor tools."""
    write_text(workspace_dir / "_CoqProject", "-R prosa prosa\n")


def workspace_coq_environment(workspace_dir: Path) -> dict[str, str]:
    """Return a self-contained environment for bare workspace-local coqc calls."""
    env = dict(os.environ)
    env.pop("COQPATH", None)
    env["ROCQPATH"] = str(workspace_dir.resolve())
    return env


def _preflight_import_commands(theorem_file: Path) -> list[str]:
    """Reuse bounded top-level imports without copying theorem-specific proof text."""
    commands: list[str] = []
    try:
        for line in theorem_file.read_text(encoding="utf-8", errors="ignore").splitlines():
            stripped = line.strip()
            if ADDITIVE_IMPORT_PATTERN.match(stripped):
                commands.append(stripped)
            if len(commands) >= 24:
                break
    except OSError:
        return []
    return commands


def toolchain_preflight(
    workspace_dir: Path,
    theorem_file: Path,
    env: dict[str, str],
    opencode_bin: str,
) -> dict:
    """Verify the exact worker environment before any model request can consume tokens."""
    started = time.time()
    manifest: dict = {
        "checked_at": now_iso(),
        "workspace": str(workspace_dir.resolve()),
        "project_file": str((workspace_dir / "_CoqProject").resolve()),
        "rocqpath": env.get("ROCQPATH"),
        "path": env.get("PATH"),
        "ok": False,
    }
    coqc = shutil.which("coqc", path=env.get("PATH"))
    opencode = Path(opencode_bin).expanduser()
    manifest["coqc"] = coqc
    manifest["opencode_bin"] = str(opencode)
    if coqc is None:
        manifest["failure_kind"] = "compiler_not_found"
        manifest["error"] = "coqc is not resolvable in the worker PATH"
        return manifest
    if not opencode.is_file() or not os.access(opencode, os.X_OK):
        manifest["failure_kind"] = "opencode_not_executable"
        manifest["error"] = f"OpenCode runner is missing or not executable: {opencode}"
        return manifest
    if not (workspace_dir / "_CoqProject").is_file():
        manifest["failure_kind"] = "project_mapping_missing"
        manifest["error"] = "staged workspace has no _CoqProject"
        return manifest

    for label, command in (
        ("version", [coqc, "--version"]),
        ("where", [coqc, "-where"]),
    ):
        try:
            result = subprocess.run(
                command,
                cwd=str(workspace_dir),
                env=env,
                capture_output=True,
                text=True,
                timeout=30,
            )
        except (OSError, subprocess.TimeoutExpired) as exc:
            manifest["failure_kind"] = f"compiler_{label}_failed"
            manifest["error"] = f"{type(exc).__name__}: {exc}"
            return manifest
        manifest[label] = (result.stdout or result.stderr).strip()[:2000]
        if result.returncode != 0:
            manifest["failure_kind"] = f"compiler_{label}_failed"
            manifest["error"] = (result.stderr or result.stdout or "unknown compiler error")[:2000]
            return manifest

    smoke_file = workspace_dir / "ProsabuddyToolchainPreflight.v"
    imports = _preflight_import_commands(theorem_file)
    smoke_source = "\n".join([
        *imports,
        "Goal True.",
        "  exact I.",
        "Qed.",
        "",
    ])
    write_text(smoke_file, smoke_source)
    try:
        result = subprocess.run(
            [coqc, smoke_file.name],
            cwd=str(workspace_dir),
            env=env,
            capture_output=True,
            text=True,
            timeout=120,
        )
        manifest["smoke_import_count"] = len(imports)
        manifest["smoke_command"] = [coqc, smoke_file.name]
        manifest["smoke_exit_code"] = result.returncode
        if result.returncode != 0:
            manifest["failure_kind"] = "smoke_compile_failed"
            manifest["error"] = (result.stderr or result.stdout or "unknown compiler error")[:4000]
            return manifest
    except (OSError, subprocess.TimeoutExpired) as exc:
        manifest["failure_kind"] = "smoke_compile_failed"
        manifest["error"] = f"{type(exc).__name__}: {exc}"
        return manifest
    finally:
        for suffix in (".v", ".vo", ".vos", ".vok", ".glob", ".aux"):
            path = smoke_file.with_suffix(suffix)
            try:
                path.unlink()
            except FileNotFoundError:
                pass
        hidden_aux = workspace_dir / f".{smoke_file.stem}.aux"
        try:
            hidden_aux.unlink()
        except FileNotFoundError:
            pass

    manifest["ok"] = True
    manifest["elapsed_seconds"] = round(time.time() - started, 3)
    return manifest


def cleanup_workspace_runtime_artifacts(workspace_dir: Path) -> list[str]:
    """Remove OpenCode dependency caches without following generated symlinks."""
    opencode_dir = workspace_dir / ".opencode"
    removed: list[str] = []
    for name in ("node_modules", "package.json", "bun.lock", ".gitignore"):
        path = opencode_dir / name
        if path.is_symlink() or path.is_file():
            path.unlink()
        elif path.is_dir():
            shutil.rmtree(path)
        else:
            continue
        removed.append(f".opencode/{name}")
    return removed


def is_paper_artifact(path: Path) -> bool:
    return path.suffix.lower() in PAPER_ARTIFACT_SUFFIXES


def prune_paper_artifacts(root: Path) -> None:
    for path in sorted(root.rglob("*"), reverse=True):
        if path.is_file() and is_paper_artifact(path):
            path.unlink()


def stage_proof_tex_alias(source_workspace_dir: Path, source_theorem_file: Path, workspace_dir: Path) -> None:
    proof_dest = workspace_dir / "proof.tex"
    if proof_dest.is_file() or source_workspace_dir.is_file():
        return

    candidates = [
        source_workspace_dir / "proof.tex",
        source_workspace_dir / f"{source_theorem_file.stem}_proof.tex",
    ]
    candidates.extend(sorted(source_workspace_dir.glob("*_proof.tex")))

    seen: set[Path] = set()
    for candidate in candidates:
        candidate = candidate.resolve()
        if candidate in seen:
            continue
        seen.add(candidate)
        if candidate.is_file():
            shutil.copy2(candidate, proof_dest)
            return


def stage_workspace(
    source_workspace_dir: Path,
    run_dir: Path,
    *,
    stage_full_casestudy_workspace: bool = False,
    full_prosa: bool = False,
    full_prosa_source_dir: Path = FULL_PROSA_SOURCE_ROOT,
) -> tuple[Path, Path]:
    """Stage either a minimal or full-source workspace for a casestudy."""
    source_theorem_file = root_theorem_file(source_workspace_dir)
    if not full_prosa and not PROSA_SOURCE_ROOT.is_dir():
        raise RuntimeError(f"Missing v06 prosa root: {PROSA_SOURCE_ROOT}")
    workspace_dir = run_dir / "workspace"
    if workspace_dir.exists():
        shutil.rmtree(workspace_dir)
    workspace_dir.mkdir(parents=True, exist_ok=True)
    prosa_dest = workspace_dir / "prosa"

    if stage_full_casestudy_workspace:
        if source_workspace_dir.is_file():
            staged_theorem_file = workspace_dir / source_theorem_file.name
            shutil.copy2(source_theorem_file, staged_theorem_file)
        else:
            for child in source_workspace_dir.iterdir():
                if child.name == "prosa":
                    continue
                destination = workspace_dir / child.name
                if child.is_dir():
                    shutil.copytree(child, destination, symlinks=True)
                else:
                    shutil.copy2(child, destination)
            staged_theorem_file = workspace_dir / source_theorem_file.name

        if not staged_theorem_file.is_file():
            raise RuntimeError(
                f"Staged theorem file missing after full workspace copy: {staged_theorem_file}"
            )

        stage_proof_tex_alias(source_workspace_dir, source_theorem_file, workspace_dir)

        if full_prosa:
            copy_full_prosa_project(full_prosa_source_dir, prosa_dest)
        else:
            # Recompute the minimal Prosa subset from the staged theorem file
            # even when the source casestudy already ships a prosa/ directory.
            copy_minimal_prosa_project(
                staged_theorem_file,
                PROSA_SOURCE_ROOT,
                prosa_dest,
                overwrite=True,
            )
        write_workspace_coq_project(workspace_dir)
        return workspace_dir, staged_theorem_file

    theorem_kind = target_theorem_kind(source_theorem_file)
    staged_theorem_file = workspace_dir / f"{theorem_kind}{source_theorem_file.suffix}"
    shutil.copy2(source_theorem_file, staged_theorem_file)

    if full_prosa:
        copy_full_prosa_project(full_prosa_source_dir, prosa_dest)
    else:
        copy_minimal_prosa_project(
            staged_theorem_file,
            PROSA_SOURCE_ROOT,
            prosa_dest,
            overwrite=True,
        )
    prune_paper_artifacts(workspace_dir)
    write_workspace_coq_project(workspace_dir)
    return workspace_dir, staged_theorem_file


def stage_workspace_skill(skill_source_dir: Path, workspace_dir: Path) -> Path:
    """Copy workspace-local skills into the staged workspace."""
    if not skill_source_dir.is_dir():
        raise RuntimeError(f"Skill source directory not found: {skill_source_dir}")

    skill_dest_dir = workspace_dir / ".opencode" / "skill"
    shutil.copytree(skill_source_dir, skill_dest_dir, dirs_exist_ok=True)
    return skill_dest_dir


# ---------------------------------------------------------------------------
# opencode.jsonc generation
# ---------------------------------------------------------------------------


def write_opencode_config(workspace_dir: Path, theorem_filename: str, *, enable_skill: bool = False) -> None:
    """Write .opencode/opencode.jsonc restricting file access and bash usage."""
    opencode_dir = workspace_dir / ".opencode"
    opencode_dir.mkdir(parents=True, exist_ok=True)

    config = {
        "$schema": "https://opencode.ai/config.json",
    }
    if enable_skill:
        config["skills"] = {"paths": [".opencode/skill"]}

    permission = {
        "codesearch": "allow",
        "lsp": "deny",
        "question": "deny",
        "task": "allow",
        "webfetch": "deny",
        "websearch": "deny",
        "bash": {
            f"coqc {theorem_filename}": "allow",
            "coqc *": "allow",
        },
    }
    if not enable_skill:
        permission["skill"] = "deny"

    config["permission"] = permission
    config_text = json.dumps(config, indent=2, ensure_ascii=False)
    write_text(opencode_dir / "opencode.jsonc", config_text)


# ---------------------------------------------------------------------------
# Run a single workspace
# ---------------------------------------------------------------------------


def _positive_env_int(name: str, default: int) -> int:
    try:
        value = int(os.environ.get(name, str(default)))
    except ValueError:
        return default
    return value if value > 0 else default


MAX_TOTAL_TOKENS = _positive_env_int("OPENCODE_MAX_TOTAL_TOKENS", 80_000_000)
MAX_AGENT_RETRIES = _positive_env_int("OPENCODE_MAX_RETRIES", 8)
MODEL_RESPONSE_TIMEOUT_SECONDS = _positive_env_int(
    "OPENCODE_MODEL_RESPONSE_TIMEOUT_SECONDS", 10 * 60
)
MAX_CONSECUTIVE_NOOP_RECOVERIES = _positive_env_int(
    "OPENCODE_MAX_CONSECUTIVE_NOOP_RECOVERIES", 5
)
MAX_CONSECUTIVE_UNCHANGED_PRODUCTIVE_ATTEMPTS = 2
MAX_IDENTICAL_THEOREM_FINGERPRINT_ATTEMPTS = 5


def _same_session_retry_or_fresh(
    current_session_id: str | None,
    tracked_session_id: str | None,
    tracked_streak: int,
) -> tuple[str | None, int, bool]:
    """Retry one same-session recovery before paying for a cold session."""
    if current_session_id and current_session_id == tracked_session_id:
        next_streak = tracked_streak + 1
    else:
        tracked_session_id = current_session_id
        next_streak = 1
    use_fresh_session = current_session_id is None or next_streak >= 2
    return tracked_session_id, next_streak, use_fresh_session


def _first_attempt_override_section(theorem_file: Path) -> str:
    return (
        "\n\n## First Attempt Phase Override\n\n"
        "For this first attempt only, the instructions in this section override any conflicting generic benchmark restriction above.\n\n"
        "- You MUST read `proof.tex` first if it exists in the current workspace.\n"
        "- This first attempt is a theorem-structure pass: your immediate goal is to translate `proof.tex` into a faithful multi-step proof skeleton inside the target theorem body before deep lemma search.\n"
        "- You are the main theorem-level agent for this pass. Work through the proof narrative and theorem body at extremely fine granularity, line by line when needed, and materialize every introduced variable, witness, notation, set, interval, equality, inequality, bridge claim, and case split as explicit Coq code before moving on.\n"
        "- Write each first-level proof module, branch, or sublemma-sized paper step as its own explicit Coq focus block `{ ... }` so the split is visible in the file.\n"
        "- For every object or bridge sentence introduced by `proof.tex`, emit the corresponding local `pose`, `set`, `have`, or `assert` statement in the file before you leave the surrounding step unresolved. Do not hide those steps only in comments.\n"
        "- Do NOT use placeholder claims such as `have H : True`, dummy names, or comment-only summaries to stand in for the paper's intermediate facts. Each named local step must carry its intended Coq term or proposition.\n"
        "- If one paper paragraph contains multiple inferential sentences, split them into multiple local named steps; a first-level `{ ... }` block is too coarse if it swallows several bridge facts that could already be stated separately.\n"
        "- If one proof sentence introduces multiple objects or performs multiple transformations, split that sentence into multiple consecutive local Coq lines instead of compressing them into one coarse step.\n"
        "- Wrap each first-level local pending obligation with `(* proof_region begin owner: lemma admit_id: <stable_id> theorem: <theorem_name> kind: <kind> target: <target_name> plan_node: <node_id> depends_on: <deps> source: <source> input: <inputs> output: <output> layer: <layer> expected: <method> normal_form: <coq_goal_shape> evidence: <prosa_or_mathcomp_evidence> *)` immediately before the exported local `have`/`assert`/`suff` statement, and `(* proof_region end admit_id: <stable_id> *)` immediately after that statement's complete `{ ... }` proof block.\n"
        "- The `normal_form` field is a locality gate, not a prose description. It must be the same Coq proposition shape as the exported target statement after harmless notation normalization; do not write vague labels such as `equality of nat sums`, `Prop disjunction`, or `sum equality`.\n"
        "- Each first-level `proof_region` must own exactly one local pending theorem-level gap, marked by one stable `admit.` or `by admit.` site with an adjacent `admit_id` comment. Do not place sibling first-level gaps in the same region.\n"
        "- Use nested `{ ... }` blocks only for true local recursion inside one already-owned gap; sibling theorem-level modules must stay in separate brace-delimited blocks in paper order.\n"
        "- Once the theorem file contains those first-level admit-owned `proof_region owner: lemma` regions, stop manual lemma dispatch; the runtime scheduler will mechanically call the lemma agent on each unresolved region one by one in text order. If the scheduler reports `needs_subgoal_remodel` or `missing or invalid target_shape_review`, revise the stale region contract or split it into smaller regions before retrying; do not keep redispatching the same unchanged `admit_id`.\n"
        "- You MUST write that theorem-level decomposition back to the file before stopping this attempt.\n"
        "- Your job in this pass is to finish the detailed admit-based theorem decomposition. Closing each child proof belongs to the scheduler-driven lemma phase that runs after this skeleton is present in the file.\n"
        "- In this first attempt only, temporary `admit.` placeholders and a temporary final `Admitted.` terminator are allowed inside the target theorem body solely to preserve the step structure taken from `proof.tex`.\n"
        "- Do NOT use `Abort`, `Axiom`, `Hypothesis`, `Parameter`, or `Variable`.\n"
        "- Preserve the theorem statement exactly and keep all temporary gaps local to the existing proof body of the target theorem.\n"
        "- After the full first-level skeleton is in the file, you may optionally discharge obvious local steps, but preserving the proof-text decomposition is higher priority than closing the theorem in this attempt.\n"
        "- Do not report a blocker until the multi-step admit skeleton is already written into the theorem body.\n\n"
        f"{_initial_read_guidance(theorem_file)}"
    )


def build_prompt(
    theorem_file: Path,
    theorem_name: str,
    theorem_statement: str,
    *,
    enable_skill: bool = False,
    segmented_proof_workflow: bool = False,
) -> str:
    """Build the full prompt by combining template + specific instructions."""
    template = OPENCODE_PROMPT.read_text(encoding="utf-8")
    first_attempt_override = (
        _first_attempt_override_section(theorem_file)
        if segmented_proof_workflow
        else ""
    )
    skill_specific = ""
    if enable_skill:
        skill_specific = (
            "Exception to the generic hard read scope above: workspace-local skill support is enabled for this run. You may invoke skills discovered under `.opencode/skill/`, "
            "and those workspace-local skill files are permitted context for this run. Start by checking whether any available workspace-local skill is relevant to this theorem, and use the most relevant one before doing broader manual exploration. Do not read any other `.opencode` content unless it is part of using those workspace-local skills.\n\n"
        )
    shortcut_policy = (
        "Outside the temporary admit-based skeleton explicitly authorized for this first attempt, "
        "do not use Axiom, Hypothesis, Parameter, Variable, Abort, theorem weakening, or edits outside the target file. "
        "The runner will preserve a first-attempt admit skeleton so later retries can discharge it, but this is not a success condition by itself.\n\n"
        if segmented_proof_workflow
        else
        "Do not cheat: no Axiom, Hypothesis, Parameter, Variable, admit, Admitted, "
        "Abort, theorem weakening, or edits outside the target file. If you write any "
        "forbidden shortcut, the runner will delete that shortcut content from the proof body "
        "and immediately retry you with a stricter warning. Do not do this.\n\n"
    )
    completion_policy = (
        "This first attempt is complete only after the multi-step proof skeleton from `proof.tex` is written into the theorem body. "
        "The overall run is finished only when `coqc` succeeds on the target file and the theorem "
        "ends with `Qed.`. If compilation fails, continue fixing the file instead of exiting."
        if segmented_proof_workflow
        else
        "You are finished only when `coqc` succeeds on the target file and the theorem "
        "ends with `Qed.`. If compilation fails, continue fixing the file instead of exiting."
    )
    bridge_specific = (
        "A bridge-shaped blocker is not a valid stopping condition. If the next proof step is blocked by a missing bridge between the current hypotheses and the desired fact, "
        f"you must inspect {_bridge_scope_text()}, instantiate candidate lemmas against the live context, and write the smallest local pose/have/assert bridge skeleton that advances the proof. "
        "If `task` is available, use it to call helper agents for narrow bridge mining or local subproof discharge instead of stopping. Only report a remaining blocker after at least one concrete bridge edit or proof-step attempt has been written and validated.\n\n"
    )
    specific = (
        f"\n\n## Current Task\n\n"
        f"The target file is `{theorem_file.name}`.\n"
        f"The theorem to prove is `{theorem_name}`.\n\n"
        "Only edit the existing proof body of the target theorem. The exact theorem declaration and statement must remain unchanged:\n\n"
        f"```coq\n{theorem_statement}\n```\n\n"
        "The runner will reject theorem-statement changes, non-additive import edits, module-structure changes, or other text changes outside the target proof block. "
        "If a proof-body repair truly requires an import, only additive `Require Import ... .` or `From ... Require Import ... .` lines before the target theorem are tolerated. "
        "Do not add helper definitions, local sections, contexts, variables, hypotheses, parameters, lemmas, or other top-level declarations.\n\n"
        f"The current workspace is exactly the directory passed to opencode via `--dir`. "
        f"Do not read, browse, inspect, or edit anything outside this workspace.\n\n"
        f"{first_attempt_override}"
        f"{skill_specific}"
        f"{bridge_specific}"
        f"Once the theorem-level skeleton exists in the file, continue with local proof search and validate progress with:\n\n"
        f"```\ncoqc {theorem_file.name}\n```\n\n"
        f"{shortcut_policy}"
        "Do not stop, claim success, or exit early just because you wrote a proof script. "
        f"{completion_policy}"
    )
    return template + specific


def _trim_compile_error(compile_error: str | None, *, max_chars: int = 4000) -> str:
    if not compile_error:
        return ""
    trimmed = compile_error.strip()
    if not trimmed:
        return ""
    if len(trimmed) <= max_chars:
        return trimmed

    # Rocq commonly emits several kilobytes of notation warnings before the
    # actionable compiler error. Keeping only the head made continuation
    # attempts blind to the actual failing line. Preserve the final File/Error
    # diagnostic block and use any remaining space for a short prefix.
    lines = trimmed.splitlines()
    error_line = next(
        (index for index in range(len(lines) - 1, -1, -1) if re.match(r"^\s*(?:Error:|Anomaly:|Fatal error:)", lines[index])),
        None,
    )
    if error_line is not None:
        diagnostic_start = error_line
        for index in range(error_line - 1, max(-1, error_line - 8), -1):
            if re.match(r'^\s*File "[^"]+", line \d+', lines[index]):
                diagnostic_start = index
                break
        diagnostic = "\n".join(lines[diagnostic_start:]).strip()
        if len(diagnostic) >= max_chars:
            return diagnostic[-max_chars:]
        marker = "[earlier Rocq warnings omitted]\n"
        prefix_budget = max_chars - len(diagnostic) - len(marker)
        prefix = "\n".join(lines[:8]).strip()
        if len(prefix) > prefix_budget:
            prefix = prefix[:max(0, prefix_budget)]
        return f"{prefix}\n{marker}{diagnostic}".strip()

    # No structured Error block was found (for example, a process-level
    # failure). Preserve both ends instead of silently discarding the tail.
    marker = "\n[... compiler output omitted ...]\n"
    budget = max_chars - len(marker)
    head = max(0, budget // 3)
    return trimmed[:head] + marker + trimmed[-(budget - head):]


def _compact_resume_history(json_log: Path, *, max_chars: int = 12000) -> str:
    """Build a compact, deterministic history snapshot from previous opencode events."""
    candidate_logs = [json_log.with_name(f"{json_log.name}.pre_fresh_resume"), json_log]
    texts: list[str] = []
    for path in candidate_logs:
        if not path.is_file():
            continue
        try:
            with path.open("r", encoding="utf-8", errors="ignore") as handle:
                for raw_line in handle:
                    try:
                        event = json.loads(raw_line)
                    except json.JSONDecodeError:
                        continue
                    if event.get("type") != "text":
                        continue
                    part = event.get("part")
                    if not isinstance(part, dict):
                        continue
                    text = part.get("text") or part.get("content")
                    if isinstance(text, str) and text.strip():
                        texts.append(re.sub(r"\s+", " ", text.strip()))
        except OSError:
            continue

    if not texts:
        return ""

    # Session-local workflow guards (for example, an exhausted one-revision
    # budget) are deliberately reset by ``--fresh-session-on-resume``.  Copying
    # the old model's terminal refusal into the new prompt recreates the stale
    # state in natural language and can make every fresh session refuse to call
    # proof_plan.  Preserve the actionable validation errors, not the obsolete
    # prohibition.
    stale_guard_markers = (
        "semantic revision is exhausted",
        "semantic revision was exhausted",
        "single permitted semantic revision",
        "must not call `proof_plan` again",
        "must not call proof_plan again",
        "active decomposition constraints",
        "exhausted-decomposition",
    )
    stale_guard_detected = False
    terminal_route_refusal_detected = False
    stale_error_hints: set[str] = set()
    filtered_texts: list[str] = []
    for text in texts:
        lower = text.lower()
        stale_guard_text = any(marker in lower for marker in stale_guard_markers) or (
            ("proof_plan" in lower or "decomposition" in lower)
            and ("exhaust" in lower or "must not" in lower or "forbidden" in lower)
        )
        if stale_guard_text:
            stale_guard_detected = True
            if "bound_root_goal_mismatch" in lower:
                stale_error_hints.add(
                    "The prior plan used an instantiated root goal; use the full quantified theorem statement as root_goal."
                )
            if "unknown_edge_endpoint" in lower:
                stale_error_hints.add(
                    "The prior plan referenced an undeclared DAG node; every edge endpoint must name a declared node."
                )
            continue

        # A model's terminal claim that the theorem is false or needs a
        # stronger statement is not a compiler certificate.  Replaying that
        # prose into every fresh session anchors later attempts on the same
        # abandoned route, even when a directly relevant library theorem has
        # not yet received an exact premise audit.  Keep such claims out of
        # the handoff; the persistent route ledger and current Coq state are
        # the authoritative sources for verified route failures.
        terminal_refusal_markers = (
            "cannot complete this theorem",
            "cannot be completed soundly",
            "cannot soundly complete",
            "cannot complete `",
            "cannot finish this theorem",
            "cannot be proved",
            "not provable as stated",
            "not provable under",
            "no sound proof",
            "no valid compiled",
            "the theorem is false",
            "mathematically invalid",
            "forward implication is therefore false",
            "required implication is false",
            "remaining obligation is false",
            "not derivable from the available hypotheses",
            "not derivable from the current context",
            "change the theorem",
            "change_theorem_spine",
            "changing the theorem statement",
            "requires changing the theorem",
            "theorem-statement/context repair",
            "add/thread a premise",
            "add an assumption",
            "add or expose a premise",
            "replacing the final terminator with `qed.` would be unsound",
            "those changes are prohibited",
        )
        structured_route_refusal = (
            "<proof_result>" in lower
            and ("\"status\":\"escalate\"" in lower or "\"status\": \"escalate\"" in lower)
            and (
                "suspected_wrong_target_shape" in lower
                or "recommended_action" in lower
                or "missing premise" in lower
            )
        )
        if any(marker in lower for marker in terminal_refusal_markers) or structured_route_refusal:
            terminal_route_refusal_detected = True
            continue
        filtered_texts.append(text)
    texts = filtered_texts

    if not texts and not stale_guard_detected and not terminal_route_refusal_detected:
        return ""

    def relevant(text: str) -> bool:
        lower = text.lower()
        markers = (
            "<proof_result>",
            "proof_block",
            "admit_id",
            "coqc",
            "compile",
            "blocker",
            "next",
            "current file status",
            "status",
            "solved",
            "failed",
        )
        return any(marker in lower for marker in markers)

    selected: list[str] = []
    if texts:
        selected.append(texts[0])
        selected.extend(text for text in texts if relevant(text))
        selected.extend(texts[-12:])

    deduped: list[str] = []
    seen: set[str] = set()
    for text in selected:
        if text in seen:
            continue
        seen.add(text)
        if len(text) > 1800:
            text = f"{text[:1400]} ... [truncated] ... {text[-300:]}"
        deduped.append(text)

    lines = [
        "## Prior Session History Compaction",
        "The following compacted history was reconstructed from the previous opencode event log. Treat the current files as authoritative if anything differs.",
        "",
    ]
    if stale_guard_detected:
        lines.extend([
            "Fresh-session recovery reset the prior session's decomposition/revision guard. Do not carry forward any old claim that proof_plan or replanning is forbidden; submit a corrected plan when the current file still lacks a valid skeleton.",
            *sorted(stale_error_hints),
            "",
        ])
    if terminal_route_refusal_detected:
        lines.extend([
            "Earlier model sessions terminated after asserting that a route or the theorem was unprovable. Treat those assertions as unverified route failures, not as theorem facts, and do not repeat them as a reason to stop.",
            "Before any new escalation, inspect the exact current proof region and mechanically audit directly relevant library lemmas with Check/About, including all residual premises and their availability in the live context. A failed instantiation rules out only that instantiation, not the theorem.",
            "",
        ])
    for index, text in enumerate(deduped, 1):
        entry = f"{index}. {text}"
        if sum(len(line) + 1 for line in lines) + len(entry) + 1 > max_chars:
            break
        lines.append(entry)
    return "\n".join(lines).strip()


def _archive_fresh_resume_log(path: Path) -> None:
    if not path.exists():
        return
    archived = path.with_name(f"{path.name}.pre_fresh_resume")
    try:
        size = path.stat().st_size
    except OSError:
        size = 0
    if size <= 0:
        path.unlink(missing_ok=True)
        return
    if archived.exists():
        stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        archived.rename(path.with_name(f"{path.name}.pre_fresh_resume.{stamp}"))
    path.rename(archived)


def build_continuation_prompt(
    theorem_file: Path,
    theorem_name: str,
    theorem_statement: str,
    *,
    proof_info: dict | None = None,
    retry_index: int,
    max_retries: int,
    enable_skill: bool = False,
    segmented_proof_workflow: bool = False,
    history_compaction: str = "",
) -> str:
    """Prompt sent when continuing a session that ended prematurely."""
    compile_error = _trim_compile_error((proof_info or {}).get("compile_error"))
    compile_error_section = ""
    if compile_error:
        compile_error_section = (
            "The runner re-checked compilation after your previous exit and it still fails:\n\n"
            f"```\n{compile_error}\n```\n\n"
        )

    shortcut_section = ""
    if (proof_info or {}).get("shortcut_removed"):
        shortcut_section = (
            "Your previous attempt used forbidden shortcut content such as `Admitted`, `Abort`, "
            "`admit`, `Axiom`, `Hypothesis`, `Parameter`, or `Variable`. "
            "The runner deleted that shortcut content from the proof body before resuming you. "
            "Do not reintroduce any forbidden shortcut. Continue from the cleaned proof and finish "
            "with a real proof ending in `Qed.`.\n\n"
        )

    skeleton_section = ""
    if segmented_proof_workflow and (proof_info or {}).get("admit_skeleton_retained"):
        skeleton_section = (
            "The first attempt was the theorem-structure pass. The current theorem body may already contain a multi-step admit-based skeleton derived from `proof.tex`. "
            "Preserve that decomposition, keep the existing first-level gaps stable, keep each first-level module inside its existing brace-delimited `{ ... }` block, rewrite any stale first-level `proof_block` header into the current `proof_region owner: lemma` form while preserving `admit_id` and block boundaries, and now discharge those gaps one region at a time instead of restarting from a blank proof. "
            "At the start of a fresh or recovered model session, if `proof.tex` has not yet been read in that live session, you MUST first use the read tool on `proof.tex` and then on the current theorem file before calling `task` or attempting any lemma dispatch. This is a session-state synchronization step; do not recreate or broaden the existing decomposition. "
            "Do not manually call `lemma` for those first-level blocks; the runtime scheduler will dispatch unresolved `owner: lemma` blocks in file order. "
            "Once that paper anchor is registered in the live session, do not reread it repeatedly. Temporary admits are no longer an acceptable final state for this retry.\n\n"
        )
    elif segmented_proof_workflow and (proof_info or {}).get("missing_segmented_skeleton"):
        skeleton_section = (
            "The previous theorem-structure pass failed to materialize a valid segmented skeleton: a bare theorem terminator such as `Admitted.` is not a proof skeleton. "
            "This is a skeleton-recovery turn; the runner may preserve the current model session once before using a fresh session. Rebuild the theorem body as explicit first-level `proof_region owner: lemma` blocks, each wrapping one exported local target statement and one local `admit.` placeholder, before attempting lemma delegation. "
            "Before any `task` or lemma dispatch, read `proof.tex` if it has not yet been read in this live session, then read the current theorem file so the paper-anchor and source-revision guards are synchronized. "
            "Do not stop again until that segmented structure is present in the file.\n\n"
        )

    plan_generation_section = ""
    plan_generation_recovery = (proof_info or {}).get("decomposition_plan_generation_recovery")
    if isinstance(plan_generation_recovery, dict):
        blockers = plan_generation_recovery.get("blockers")
        blocker_lines = ""
        if isinstance(blockers, list) and blockers:
            blocker_lines = "\n".join(
                f"- {str(blocker)[:500]}" for blocker in blockers[:8]
            )
        plan_generation_section = (
            "The previous bounded proof-plan generation was rejected, but the workflow authorized one more planning generation in this same model session. "
            "Use the persisted best rejected plan as diagnostic input only; submit a materially corrected structured DAG and do not materialize a rejected plan.\n"
            + (f"The strongest current blockers are:\n{blocker_lines}\n" if blocker_lines else "")
            + "Do not stop merely because the earlier generation exhausted; the next proof_plan call activates the bounded recovery generation.\n\n"
        )

    plan_generation_fresh_attempt = (proof_info or {}).get(
        "decomposition_terminal_fresh_attempt"
    )
    if isinstance(plan_generation_fresh_attempt, dict):
        blockers = plan_generation_fresh_attempt.get("blockers")
        blocker_lines = ""
        if isinstance(blockers, list) and blockers:
            blocker_lines = "\n".join(
                f"- {str(blocker)[:500]}" for blocker in blockers[:8]
            )
        failed_fingerprint = str(
            plan_generation_fresh_attempt.get("semantic_fingerprint")
            or plan_generation_fresh_attempt.get("best_semantic_fingerprint")
            or ""
        )
        plan_generation_section += (
            "The previous proof-planning session exhausted its bounded recovery generations. "
            "This starts a fresh proof attempt; it is not completion of the experiment and it does not reset the workspace. "
            "Treat the current theorem file and compiler-certified regions as authoritative, and preserve valid work already present. "
            "Use the blockers below as diagnostic input, but submit a materially different plan or continue with compiler-driven proof work instead of repeating the rejected semantic route. "
            "Do not reject harmless target normalization without concrete Coq/compiler evidence.\n"
            + (
                f"Rejected semantic fingerprint (do not repeat unchanged): {failed_fingerprint}\n"
                if failed_fingerprint
                else ""
            )
            + (f"The strongest current blockers are:\n{blocker_lines}\n" if blocker_lines else "")
            + "\n"
        )

    semantic_livelock_section = ""
    semantic_livelock_recovery = (proof_info or {}).get("semantic_livelock_recovery")
    if isinstance(semantic_livelock_recovery, dict):
        repeated_fingerprint = str(semantic_livelock_recovery.get("file_fingerprint") or "")
        repeated_attempts = int(semantic_livelock_recovery.get("identical_attempts") or 0)
        semantic_livelock_section = (
            "The runner observed five productive invocations that all ended with the exact same theorem source and unresolved segmented proof skeleton. "
            "This is a route-remodel handoff, not another ordinary continuation. Preserve compiler-certified regions, but change the semantic route, missing bridge, or proof-region contract before delegating again. "
            "Do not spend this turn merely rereading the same files, renaming admit_id markers, or launching the same repair child. "
            f"Repeated source fingerprint: {repeated_fingerprint}; identical attempts: {repeated_attempts}. "
            "If the current split is still appropriate, materialize one concrete proof-producing change and validate it; otherwise revise only the affected region/dependency slice.\n\n"
        )

    reasoning_exhaustion_section = ""
    reasoning_exhaustion_recovery = (proof_info or {}).get(
        "reasoning_output_exhausted_recovery"
    )
    if isinstance(reasoning_exhaustion_recovery, dict):
        exhaustion_count = int(
            reasoning_exhaustion_recovery.get("consecutive_exhaustions") or 0
        )
        reasoning_exhaustion_section = (
            "The previous model response exhausted its output allowance in hidden reasoning "
            "and was truncated before it emitted any assistant text or tool call. This is a "
            "recovery turn, not evidence that the proof is complete or blocked. Keep the analysis "
            "compact and make the first externally visible action a tool call: read `proof.tex` "
            "first only if this fresh session has not read it, then read the current target proof "
            "region or run the compiler/checkpoint needed for the next concrete edit. Do not spend "
            "the entire response restating the theorem or planning without using a tool. "
            f"Consecutive reasoning-only truncations in the current recovery batch: {exhaustion_count}.\n\n"
        )

    skill_specific = ""
    if enable_skill:
        skill_specific = (
            "Exception to the generic hard read scope above: workspace-local skill support remains enabled for this run. You may continue using skills discovered under `.opencode/skill/`, "
            "and those workspace-local skill files are permitted context. Do not read any other `.opencode` content unless it is part of using those workspace-local skills.\n\n"
        )
    bridge_specific = (
        f"Your previous stop does not count as completion. If you hit a missing-bridge blocker, resume by mining {_bridge_scope_text()}, "
        "instantiate candidate lemmas, and write the smallest local bridge skeleton that can be validated. If `task` is available, use helper agents for narrow bridge mining or local subproof discharge instead of stopping again.\n\n"
        "Keep compiler feedback close to proof edits: after a proof-producing edit, make at most one additional corrective proof edit before calling `checkpoint` or `coqc`. "
        "After a stale-edit conflict, reread the exact current region once, apply the replacement, and validate it before another rewrite. "
        "Do not repeatedly reread or replace an unvalidated whole theorem body.\n\n"
    )
    history_section = f"{history_compaction}\n\n" if history_compaction else ""

    return (
        f"The previous conversation ended but the proof is NOT yet complete.\n\n"
        f"The target file is `{theorem_file.name}`, the theorem is `{theorem_name}`.\n\n"
        "Only edit the existing proof body of the target theorem. The exact theorem declaration and statement must remain unchanged:\n\n"
        f"```coq\n{theorem_statement}\n```\n\n"
        f"This is retry {retry_index} of {max_retries}. Do not exit until `coqc {theorem_file.name}` succeeds.\n\n"
        f"{history_section}{plan_generation_section}{semantic_livelock_section}{reasoning_exhaustion_section}{skeleton_section}{shortcut_section}{compile_error_section}{skill_specific}{bridge_specific}"
        f"Please continue working. Read the current state of `{theorem_file.name}`, "
        f"fix the remaining proof or compilation issues, and keep iterating until `coqc {theorem_file.name}` "
        f"compiles successfully with the proof ending in `Qed.`.\n\n"
        "Do not cheat, do not weaken the theorem, do not add assumptions or placeholders, "
        "do not add top-level declarations or rewrite the surrounding file structure beyond an additive import line that is strictly required before the target theorem, "
        "and do not inspect or modify anything outside the staged workspace."
    )


def _preserve_first_attempt_admit_skeleton(proof_info: dict) -> bool:
    has_admit_skeleton = bool(proof_info.get("has_admit") or proof_info.get("has_admitted"))
    has_disallowed_shortcut = bool(proof_info.get("has_abort") or proof_info.get("has_axiom"))
    has_segmented_skeleton = bool(proof_info.get("has_segmented_proof_region_skeleton"))
    return has_admit_skeleton and has_segmented_skeleton and not has_disallowed_shortcut


def _has_segmented_proof_region_skeleton(proof_body: str) -> bool:
    return bool(
        re.search(r"\(\*\s*proof_region\s+begin\b[\s\S]*?\bowner:\s*lemma\b", proof_body)
        and re.search(r"\badmit\s*\.", proof_body)
    )


# ---------------------------------------------------------------------------
# Proof verification
# ---------------------------------------------------------------------------


def check_proof_success(
    source_theorem_file: Path,
    workspace_dir: Path,
    theorem_file: Path,
) -> tuple[bool, dict]:
    """Check if theorem file has Qed and compiles. Returns (success, info_dict)."""
    info: dict = {}
    try:
        final_text = theorem_file.read_text(encoding="utf-8", errors="ignore")
        integrity_info = inspect_theorem_edit_integrity(source_theorem_file, theorem_file)
        info.update(integrity_info)
        if integrity_info.get("compile_error", "").startswith("Unauthorized file modification:"):
            info["spec_violation_error"] = info.pop("compile_error")
        if integrity_info.get("integrity_check_failed"):
            info["proof_verified"] = False
            return False, info

        theorem_kind = target_theorem_kind(source_theorem_file)
        theorem_name = target_theorem_name(source_theorem_file)
        ranges = _extract_target_theorem_ranges(final_text, theorem_kind, theorem_name)
        if ranges is None:
            source_text = source_theorem_file.read_text(encoding="utf-8", errors="ignore")
            source_ranges = _extract_target_theorem_ranges(source_text, theorem_kind, theorem_name)
            source_suffix = source_text[source_ranges[3]:] if source_ranges else ""
            if source_suffix:
                ranges = _extract_target_theorem_ranges(
                    final_text,
                    theorem_kind,
                    theorem_name,
                    allow_unterminated=True,
                    theorem_suffix=source_suffix,
                )
        if ranges is None:
            info["proof_verified"] = False
            info["compile_error"] = (
                f"Runner error: could not locate the target theorem `{theorem_name}` in the staged file."
            )
            return False, info
        if info.get("target_proof_unterminated"):
            info.setdefault("compile_error", _unterminated_proof_message(theorem_name))

        _decl_start, _statement_end, body_start, body_end = ranges
        proof_body = final_text[body_start:body_end]

        has_qed = bool(re.search(r"\bQed\.", proof_body))
        has_admitted = bool(re.search(r"\bAdmitted\.", proof_body))
        has_abort = bool(re.search(r"\bAbort\.", proof_body))
        has_admit = bool(re.search(r"\badmit\b", proof_body))
        has_axiom = bool(
            re.search(r"^\s*(?:Local\s+)?(Axiom|Hypothesis|Parameter|Variable)\b", proof_body, re.MULTILINE)
        )
        has_forbidden_shortcut = has_admitted or has_abort or has_admit or has_axiom
        has_segmented_proof_region_skeleton = _has_segmented_proof_region_skeleton(proof_body)

        info["has_qed"] = has_qed
        info["has_segmented_proof_region_skeleton"] = has_segmented_proof_region_skeleton
        if has_admitted:
            info["has_admitted"] = True
        if has_abort:
            info["has_abort"] = True
        if has_admit:
            info["has_admit"] = True
        if has_axiom:
            info["has_axiom"] = True
        if has_forbidden_shortcut:
            info["has_forbidden_shortcut"] = True

        if has_qed and not has_forbidden_shortcut:
            try:
                compile_result = subprocess.run(
                    ["coqc", theorem_file.name],
                    cwd=str(workspace_dir),
                    env=workspace_coq_environment(workspace_dir),
                    capture_output=True,
                    text=True,
                    timeout=300,
                )
                if compile_result.returncode == 0:
                    info["proof_verified"] = True
                    return True, info
                else:
                    info["proof_verified"] = False
                    info["compile_error"] = _trim_compile_error(compile_result.stderr)
            except Exception as e:
                info["proof_verified"] = False
                info["compile_error"] = str(e)
        else:
            info["proof_verified"] = False
    except Exception:
        pass
    return False, info


def _sanitize_forbidden_shortcuts_in_proof_body(proof_body: str) -> tuple[str, list[str]]:
    removed_kinds: list[str] = []
    cleaned_lines: list[str] = []
    inserted_cleanup_comment = False

    def record(kind: str) -> None:
        if kind not in removed_kinds:
            removed_kinds.append(kind)

    def cleanup_comment(line: str) -> str:
        indent = re.match(r"\s*", line).group(0)
        return (
            f"{indent}(* Runner removed forbidden shortcut content from the previous attempt. "
            f"Continue with a real proof. *)\n"
        )

    def replacement_line(line: str, text: str) -> str:
        newline = "\n" if line.endswith("\n") else ""
        indent = re.match(r"\s*", line).group(0)
        return f"{indent}{text}{newline}"

    lines = proof_body.splitlines(keepends=True)
    for line in lines:
        stripped = line.strip()

        if re.fullmatch(r"Admitted\.", stripped):
            record("Admitted")
            if not inserted_cleanup_comment:
                cleaned_lines.append(cleanup_comment(line))
                inserted_cleanup_comment = True
            cleaned_lines.append(replacement_line(line, "Defined."))
            continue

        if re.fullmatch(r"Abort\.", stripped):
            record("Abort")
            if not inserted_cleanup_comment:
                cleaned_lines.append(cleanup_comment(line))
                inserted_cleanup_comment = True
            cleaned_lines.append(replacement_line(line, "Defined."))
            continue

        if re.search(r"\badmit\b", line):
            record("admit")
            if not inserted_cleanup_comment:
                cleaned_lines.append(cleanup_comment(line))
                inserted_cleanup_comment = True
            continue

        shortcut_decl = re.match(r"^\s*(?:Local\s+)?(Axiom|Hypothesis|Parameter|Variable)\b", line)
        if shortcut_decl:
            record(shortcut_decl.group(1))
            if not inserted_cleanup_comment:
                cleaned_lines.append(cleanup_comment(line))
                inserted_cleanup_comment = True
            continue

        cleaned_lines.append(line)

    if not removed_kinds:
        return proof_body, removed_kinds

    cleaned_body = "".join(cleaned_lines)
    if not re.search(r"\b(Qed|Defined|Admitted)\s*\.", cleaned_body):
        newline = "\n" if cleaned_body.endswith("\n") or not cleaned_body else ""
        if not inserted_cleanup_comment:
            cleaned_body += "(* Runner removed forbidden shortcut content from the previous attempt. Continue with a real proof. *)\n"
        cleaned_body += f"Defined.{newline}"

    return cleaned_body, removed_kinds


def cleanup_forbidden_shortcuts(
    source_theorem_file: Path,
    theorem_file: Path,
    *,
    preserve_segmented_skeleton: bool = False,
) -> dict:
    info: dict = {"shortcut_removed": False}

    theorem_kind = target_theorem_kind(source_theorem_file)
    theorem_name = target_theorem_name(source_theorem_file)
    current_text = theorem_file.read_text(encoding="utf-8", errors="ignore")
    ranges = _extract_target_theorem_ranges(current_text, theorem_kind, theorem_name)
    if ranges is None:
        source_text = source_theorem_file.read_text(encoding="utf-8", errors="ignore")
        source_ranges = _extract_target_theorem_ranges(source_text, theorem_kind, theorem_name)
        source_suffix = source_text[source_ranges[3]:] if source_ranges else ""
        if source_suffix:
            ranges = _extract_target_theorem_ranges(
                current_text,
                theorem_kind,
                theorem_name,
                allow_unterminated=True,
                theorem_suffix=source_suffix,
            )
    if ranges is None:
        return info

    _decl_start, _statement_end, body_start, body_end = ranges
    proof_body = current_text[body_start:body_end]
    if preserve_segmented_skeleton and _has_segmented_proof_region_skeleton(proof_body):
        info["segmented_skeleton_preserved"] = True
        return info

    cleaned_body, removed_kinds = _sanitize_forbidden_shortcuts_in_proof_body(proof_body)
    if cleaned_body == proof_body:
        return info

    theorem_file.write_text(
        current_text[:body_start] + cleaned_body + current_text[body_end:],
        encoding="utf-8",
    )

    kinds_text = ", ".join(removed_kinds)
    info["shortcut_removed"] = True
    info["shortcut_cleanup_kinds"] = removed_kinds
    info["compile_error"] = (
        "The previous attempt used forbidden shortcut content in the proof body "
        f"({kinds_text}). The runner removed that content before retrying. "
        "Continue with a real proof ending in `Qed.`."
    )
    return info


# ---------------------------------------------------------------------------
# Token accounting from opencode JSON events
# ---------------------------------------------------------------------------


def extract_trace_usage(json_log: Path) -> tuple[str | None, int, int]:
    """Return the latest root session, cumulative tokens, and model-step count.

    The stop-budget token count intentionally matches the trace file as written:
    the sum from the first line through the latest line of
    ``opencode_events.jsonl``.
    """
    session_id: str | None = None
    total_tokens = 0
    model_steps = 0
    try:
        with json_log.open("r", encoding="utf-8", errors="ignore") as f:
            for raw_line in f:
                raw_line = raw_line.strip()
                if not raw_line:
                    continue
                try:
                    event = json.loads(raw_line)
                except json.JSONDecodeError:
                    continue
                if "sessionID" in event and not event.get("parentSessionID"):
                    session_id = event["sessionID"]
                if event.get("type") == "step_finish":
                    model_steps += 1
                    part = event.get("part", {})
                    tokens = part.get("tokens", {})
                    # Preferred metric: trace-reported per-step total.
                    # Fallback keeps compatibility with traces that omit total.
                    step_total = tokens.get("total")
                    if isinstance(step_total, (int, float)):
                        total_tokens += int(step_total)
                    else:
                        total_tokens += int(tokens.get("input", 0))
                        total_tokens += int(tokens.get("output", 0))
                        total_tokens += int(tokens.get("reasoning", 0))
    except FileNotFoundError:
        pass
    return session_id, total_tokens, model_steps


def extract_session_and_tokens(json_log: Path) -> tuple[str | None, int]:
    """Backward-compatible session/token projection of ``extract_trace_usage``."""
    usage = extract_trace_usage(json_log)
    return usage[0], usage[1]


def extract_request_trace_tokens(request_trace: Path) -> int:
    """Recover cumulative usage that may not yet have reached result.json."""
    total_tokens = 0
    seen: set[tuple[str, str, int]] = set()
    try:
        with request_trace.open("r", encoding="utf-8", errors="ignore") as f:
            for raw_line in f:
                try:
                    event = json.loads(raw_line)
                except json.JSONDecodeError:
                    continue
                if event.get("type") != "request":
                    continue
                key = (
                    str(event.get("session_id") or ""),
                    str(event.get("request_id") or ""),
                    _int_value(event.get("step")),
                )
                if key in seen:
                    continue
                seen.add(key)
                usage = event.get("usage")
                if isinstance(usage, dict):
                    total_tokens += _int_value(usage.get("total_tokens"))
    except FileNotFoundError:
        pass
    return total_tokens


def extract_attempt_request_outcome(request_trace: Path, start_size: int) -> dict:
    """Summarize provider responses appended by one runner invocation.

    Some reasoning models can spend their entire output allowance on hidden
    reasoning and terminate with ``finish.reason == "length"`` before emitting
    assistant text or a tool call.  OpenCode then has no actionable event to
    expose, so the runner must distinguish this recoverable truncation from an
    ordinary terminal no-op.
    """
    request_count = 0
    length_terminated_count = 0
    output_tokens = 0
    reasoning_tokens = 0
    finish_reasons: list[str] = []
    try:
        with request_trace.open("rb") as f:
            f.seek(max(0, start_size))
            for raw_line in f:
                try:
                    event = json.loads(raw_line.decode("utf-8", errors="ignore"))
                except (json.JSONDecodeError, UnicodeDecodeError):
                    continue
                if not isinstance(event, dict) or event.get("type") != "request":
                    continue
                request_count += 1
                finish = event.get("finish")
                if isinstance(finish, dict):
                    reason = str(finish.get("reason") or "").strip().lower()
                elif isinstance(finish, str):
                    reason = finish.strip().lower()
                else:
                    reason = ""
                if reason:
                    finish_reasons.append(reason)
                if reason == "length":
                    length_terminated_count += 1
                usage = event.get("usage")
                if isinstance(usage, dict):
                    output_tokens += _int_value(usage.get("output_tokens"))
                    reasoning_tokens += _int_value(usage.get("reasoning_tokens"))
    except FileNotFoundError:
        pass

    reasoning_fraction = (
        reasoning_tokens / output_tokens if output_tokens > 0 else 0.0
    )
    return {
        "request_count": request_count,
        "finish_reasons": finish_reasons,
        "length_terminated_count": length_terminated_count,
        "output_tokens": output_tokens,
        "reasoning_tokens": reasoning_tokens,
        "reasoning_fraction": reasoning_fraction,
        "reasoning_output_exhausted": bool(
            request_count > 0
            and length_terminated_count == request_count
            and output_tokens > 0
            and reasoning_fraction >= 0.95
        ),
    }


def _should_charge_noop_recovery(consecutive_noops: int) -> bool:
    """Bound free no-op recovery without terminating the whole experiment."""
    return consecutive_noops >= MAX_CONSECUTIVE_NOOP_RECOVERIES


def extract_attempt_tool_calls(json_log: Path, start_size: int) -> int:
    """Count distinct tool calls emitted after ``start_size``.

    A model response that only repeats a terminal/blocker message still emits
    tokens and a ``step_finish`` event.  Treating that as productive work makes
    the retry loop reuse the same exhausted session until it burns the entire
    proof-retry budget.  Tool call IDs are counted once because OpenCode emits
    both running and terminal records for the same call.
    """
    call_ids: set[str] = set()
    try:
        with json_log.open("rb") as f:
            f.seek(max(0, start_size))
            for raw_line in f:
                try:
                    event = json.loads(raw_line.decode("utf-8", errors="ignore"))
                except (json.JSONDecodeError, UnicodeDecodeError):
                    continue
                if not isinstance(event, dict) or event.get("type") != "tool_use":
                    continue
                part = event.get("part") if isinstance(event.get("part"), dict) else {}
                call_id = part.get("callID")
                if isinstance(call_id, str) and call_id:
                    call_ids.add(call_id)
    except FileNotFoundError:
        pass
    return len(call_ids)


def extract_attempt_terminal_text(json_log: Path, start_size: int) -> str:
    """Return the last assistant text emitted by one runner invocation."""
    terminal_text = ""
    try:
        with json_log.open("rb") as f:
            f.seek(max(0, start_size))
            for raw_line in f:
                try:
                    event = json.loads(raw_line.decode("utf-8", errors="ignore"))
                except (json.JSONDecodeError, UnicodeDecodeError):
                    continue
                if not isinstance(event, dict) or event.get("type") != "text":
                    continue
                part = event.get("part") if isinstance(event.get("part"), dict) else {}
                text = part.get("text") or part.get("content")
                if isinstance(text, str) and text.strip():
                    terminal_text = text.strip()
    except FileNotFoundError:
        pass
    return terminal_text


def _completed_tool_metadata(event: object, tool_names: set[str]) -> tuple[str, dict] | None:
    if not isinstance(event, dict) or event.get("type") != "tool_use":
        return None
    part = event.get("part") if isinstance(event.get("part"), dict) else {}
    tool = part.get("tool")
    state = part.get("state") if isinstance(part.get("state"), dict) else {}
    metadata = state.get("metadata") if isinstance(state.get("metadata"), dict) else None
    if tool not in tool_names or state.get("status") != "completed" or metadata is None:
        return None
    return str(tool), metadata


def _stable_payload_hash(payload: object) -> str:
    encoded = json.dumps(
        payload,
        sort_keys=True,
        separators=(",", ":"),
        ensure_ascii=False,
        default=str,
    ).encode("utf-8")
    return hashlib.sha256(encoded).hexdigest()


def _proof_transaction_runtime_state(metadata: dict, theorem_file: Path) -> dict | None:
    transaction = metadata.get("proof_edit_transaction")
    if not isinstance(transaction, dict):
        return None
    transaction_file = transaction.get("file")
    if not isinstance(transaction_file, str) or not transaction_file:
        return None
    try:
        if Path(transaction_file).resolve() != theorem_file.resolve():
            return None
    except OSError:
        return None

    source_hash = transaction.get("source_hash")
    return {
        "source_hash": source_hash if isinstance(source_hash, str) else "",
        "revision": transaction.get("revision") if isinstance(transaction.get("revision"), int) else None,
        "certified_revision": (
            transaction.get("certified_revision")
            if isinstance(transaction.get("certified_revision"), int)
            else None
        ),
        "certified_region_count": (
            transaction.get("certified_region_count")
            if isinstance(transaction.get("certified_region_count"), int)
            else None
        ),
        "certified_unresolved_debt": (
            transaction.get("certified_unresolved_debt")
            if isinstance(transaction.get("certified_unresolved_debt"), int)
            else None
        ),
        "validation_pending": transaction.get("validation_pending") is True,
        "staged": transaction.get("staged") is True,
    }


def extract_proof_runtime_state(
    json_log: Path,
    start_size: int,
    theorem_file: Path,
) -> dict:
    """Track staged transaction bytes and compiler-backed progress from tool metadata."""
    runtime_state: dict = {
        "transaction": None,
        "certificate_signature": None,
    }
    try:
        with json_log.open("rb") as stream:
            stream.seek(max(0, start_size))
            for raw_line in stream:
                try:
                    event = json.loads(raw_line.decode("utf-8", errors="ignore"))
                except (json.JSONDecodeError, UnicodeDecodeError):
                    continue
                if not isinstance(event, dict) or event.get("type") != "tool_use":
                    continue
                part = event.get("part") if isinstance(event.get("part"), dict) else {}
                tool_state = part.get("state") if isinstance(part.get("state"), dict) else {}
                metadata = tool_state.get("metadata") if isinstance(tool_state.get("metadata"), dict) else None
                if tool_state.get("status") != "completed" or metadata is None:
                    continue

                transaction_state = _proof_transaction_runtime_state(metadata, theorem_file)
                if transaction_state is not None:
                    runtime_state["transaction"] = transaction_state

                proof_status = metadata.get("proof_status")
                proof_progress = (
                    proof_status.get("proof_progress")
                    if isinstance(proof_status, dict)
                    and isinstance(proof_status.get("proof_progress"), dict)
                    else None
                )
                lifecycle = metadata.get("proof_region_lifecycle")
                accepted = bool(
                    proof_progress
                    and proof_progress.get("accepted") is True
                    and proof_progress.get("level") in {"hard", "structural"}
                )
                certified = isinstance(lifecycle, dict) and lifecycle.get("action") == "certified"
                if accepted or certified:
                    runtime_state["certificate_signature"] = _stable_payload_hash({
                        "tool": part.get("tool"),
                        "receipt": proof_progress.get("receipt") if proof_progress else None,
                        "lifecycle": lifecycle if certified else None,
                        "transaction_source_hash": (
                            transaction_state or runtime_state.get("transaction") or {}
                        ).get("source_hash"),
                    })
    except FileNotFoundError:
        pass
    return runtime_state


def merge_proof_runtime_state(current: dict, observed: dict) -> dict:
    return {
        "transaction": observed.get("transaction") or current.get("transaction"),
        "certificate_signature": (
            observed.get("certificate_signature") or current.get("certificate_signature")
        ),
    }


def proof_runtime_fingerprint(file_fingerprint: str, runtime_state: dict) -> str:
    transaction = runtime_state.get("transaction")
    transaction_identity = None
    if isinstance(transaction, dict):
        source_hash = transaction.get("source_hash")
        transaction_identity = {
            "source_hash": source_hash,
            "revision_fallback": transaction.get("revision") if not source_hash else None,
            "certified_revision": transaction.get("certified_revision"),
            "certified_region_count": transaction.get("certified_region_count"),
            "certified_unresolved_debt": transaction.get("certified_unresolved_debt"),
        }
    return _stable_payload_hash({
        "file_fingerprint": file_fingerprint,
        "transaction": transaction_identity,
        "certificate_signature": runtime_state.get("certificate_signature"),
    })


def proof_runtime_source_hashes(file_fingerprint: str, runtime_state: dict) -> set[str]:
    hashes = {file_fingerprint} if file_fingerprint else set()
    transaction = runtime_state.get("transaction")
    if isinstance(transaction, dict):
        source_hash = transaction.get("source_hash")
        if isinstance(source_hash, str) and source_hash:
            hashes.add(source_hash)
    return hashes


def extract_attempt_decomposition_terminal(json_log: Path, start_size: int) -> dict | None:
    """Return a source-bound terminal semantic verdict from one invocation."""
    terminal: dict | None = None
    try:
        with json_log.open("rb") as f:
            f.seek(max(0, start_size))
            for raw_line in f:
                try:
                    event = json.loads(raw_line.decode("utf-8", errors="ignore"))
                except (json.JSONDecodeError, UnicodeDecodeError):
                    continue
                completed = _completed_tool_metadata(event, {"proof_plan"})
                if completed is None:
                    continue
                _, metadata = completed
                verdict = metadata.get("terminal_verdict")
                if (
                    metadata.get("planning_status") == "exhausted"
                    and isinstance(verdict, dict)
                    and verdict.get("status") == "semantic_incomplete"
                ):
                    terminal = dict(verdict)
                elif metadata.get("planning_status") in {"planning", "accepted"}:
                    terminal = None
    except FileNotFoundError:
        pass
    return terminal


def extract_materialization_livelock(terminal_text: str) -> dict | None:
    """Parse the structured ProsaBuddy materialization-livelock receipt."""
    prefix = "materialization_livelock:"
    for line in terminal_text.splitlines():
        if not line.lower().startswith(prefix):
            continue
        payload = line[len(prefix):].strip()
        try:
            receipt = json.loads(payload)
        except json.JSONDecodeError:
            return {"status": "materialization_livelock", "recoverable": True}
        if isinstance(receipt, dict) and receipt.get("status") == "materialization_livelock":
            return receipt
    return None


def decomposition_terminal_receipts_enabled(
    *,
    segmented_proof_workflow: bool,
    env: dict[str, str],
) -> bool:
    """Recognize decomposition mode from either supported activation path."""
    return (
        segmented_proof_workflow
        or env.get("OPENCODE_PROOF_WORKFLOW_MODE") == "decomposition"
    )


def decomposition_terminal_recovery_strategy(
    verdict: dict,
    retry_budget_model_attempts: int,
    max_retries: int,
) -> str:
    """Map a session-scoped planning verdict to an experiment-level action."""
    if retry_budget_model_attempts >= max_retries + 1:
        return "retry_limit"
    if verdict.get("recoverable") is True:
        return "retry_same_session"
    return "fresh_session"


def extract_latest_decomposition_checkpoint(json_log: Path) -> dict | None:
    """Return the latest completed coqc/checkpoint decomposition receipt."""
    latest: dict | None = None
    try:
        with json_log.open("r", encoding="utf-8", errors="ignore") as f:
            for raw_line in f:
                try:
                    event = json.loads(raw_line)
                except json.JSONDecodeError:
                    continue
                completed = _completed_tool_metadata(event, {"coqc", "checkpoint"})
                if completed is None:
                    continue
                tool, metadata = completed
                checkpoint = metadata.get("decomposition_checkpoint")
                if not isinstance(checkpoint, dict):
                    continue
                latest = {"tool": tool, **checkpoint}
    except FileNotFoundError:
        pass
    return latest


def _read_json_file(path: Path) -> dict | None:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError, OSError):
        return None


def _read_json_payload(path: Path) -> object | None:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except (FileNotFoundError, json.JSONDecodeError, OSError):
        return None


def _read_json_list(path: Path) -> list[dict]:
    payload = _read_json_payload(path)
    if not isinstance(payload, list):
        return []
    return [item for item in payload if isinstance(item, dict)]


def _read_progress_events(progress_file: Path, workspace_name: str | None = None) -> list[dict]:
    events: list[dict] = []
    try:
        with progress_file.open("r", encoding="utf-8", errors="ignore") as f:
            for raw_line in f:
                try:
                    event = json.loads(raw_line)
                except json.JSONDecodeError:
                    continue
                if not isinstance(event, dict):
                    continue
                if workspace_name is not None and event.get("workspace") != workspace_name:
                    continue
                events.append(event)
    except FileNotFoundError:
        pass
    return events


def _opencode_session_exists(xdg_data_home: Path, session_id: str) -> bool:
    opencode_dir = xdg_data_home / "opencode"
    for db_name in ("opencode-local.db", "opencode-dev.db"):
        db_path = opencode_dir / db_name
        if not db_path.is_file():
            continue
        try:
            con = sqlite3.connect(f"file:{db_path}?mode=ro", uri=True)
            try:
                row = con.execute("select 1 from session where id = ? limit 1", (session_id,)).fetchone()
                if row:
                    return True
            finally:
                con.close()
        except sqlite3.Error:
            continue

    session_diff = opencode_dir / "storage" / "session_diff" / f"{session_id}.json"
    if session_diff.is_file():
        return True

    trace_root = opencode_dir / "trace"
    return trace_root.is_dir() and any(trace_root.glob(f"run-*/*{session_id}"))


def _candidate_resume_xdg_data_homes(
    *,
    base_run_dir: Path,
    workspace_name: str,
    session_id: str | None,
    result: dict,
    existing_summary: dict | None,
) -> list[Path]:
    candidates: list[Path] = []

    def add(value: object) -> None:
        if not isinstance(value, str) or not value:
            return
        path = Path(value).expanduser()
        if path not in candidates:
            candidates.append(path)

    add(os.environ.get("XDG_DATA_HOME"))
    add(result.get("xdg_data_home"))
    if existing_summary:
        add(existing_summary.get("xdg_data_home"))

    for event in reversed(_read_progress_events(base_run_dir / "progress.jsonl", workspace_name)):
        if session_id and event.get("session_id") not in (session_id, None):
            continue
        add(event.get("xdg_data_home"))

    return candidates


def _resolve_resume_xdg_data_home(
    *,
    base_run_dir: Path,
    workspace_name: str,
    session_id: str | None,
    result: dict,
    existing_summary: dict | None,
) -> tuple[Path | None, bool]:
    env_xdg = os.environ.get("XDG_DATA_HOME")
    if env_xdg:
        forced = Path(env_xdg).expanduser()
        if forced.is_dir():
            session_there = bool(session_id and _opencode_session_exists(forced, session_id))
            return forced, session_there

    candidates = _candidate_resume_xdg_data_homes(
        base_run_dir=base_run_dir,
        workspace_name=workspace_name,
        session_id=session_id,
        result=result,
        existing_summary=existing_summary,
    )
    existing_candidates = [path for path in candidates if path.is_dir()]

    if session_id:
        for candidate in existing_candidates:
            if _opencode_session_exists(candidate, session_id):
                return candidate, True

    return (existing_candidates[0], False) if existing_candidates else (None, False)


def _apply_xdg_data_home(env: dict[str, str], xdg_data_home: Path) -> None:
    """Point a resumed run at its persisted session database.

    The other XDG roots intentionally remain inherited.  Parallel workers may
    keep state in a sibling directory, while provider configuration and model
    cache may live in the user's normal config/cache roots.  Re-deriving those
    paths from XDG_DATA_HOME makes a valid provider disappear during resume.
    """
    env["XDG_DATA_HOME"] = str(xdg_data_home)


def _int_value(value: object, default: int = 0) -> int:
    try:
        return int(value)
    except (TypeError, ValueError):
        return default


def _float_value(value: object, default: float = 0.0) -> float:
    try:
        return float(value)
    except (TypeError, ValueError):
        return default


def _latest_progress_attempt(progress_file: Path, workspace_name: str) -> dict | None:
    """Return the latest persisted attempt counters for one workspace.

    ``result.json`` is only refreshed when a runner exits normally.  During a
    supervised restart it can therefore lag several attempts behind
    ``progress.jsonl``.  This helper provides an explicit, append-only source
    for preserving the active retry epoch without resetting it.
    """
    latest: dict | None = None
    try:
        with progress_file.open("r", encoding="utf-8", errors="ignore") as handle:
            for raw_line in handle:
                try:
                    event = json.loads(raw_line)
                except json.JSONDecodeError:
                    continue
                if not isinstance(event, dict):
                    continue
                if event.get("event") != "attempt" or event.get("workspace") != workspace_name:
                    continue
                latest = event
    except OSError:
        return None
    return latest


def _apply_resume_config_defaults(options: dict, resume_config: dict) -> None:
    explicit_numeric_options = options.get("_explicit_numeric_options")
    if not isinstance(explicit_numeric_options, set):
        explicit_numeric_options = set()

    for key in (
        "run_timeout_seconds",
        "model_response_timeout_seconds",
        "max_total_tokens",
        "max_retries",
    ):
        if key in explicit_numeric_options:
            continue
        value = _int_value(resume_config.get(key))
        if value > 0:
            options[key] = value

    cases_dir = resume_config.get("cases_dir")
    if isinstance(cases_dir, str) and cases_dir:
        options["cases_dir"] = cases_dir

    if "stage_full_casestudy_workspace" in resume_config:
        options["stage_full_casestudy_workspace"] = bool(resume_config.get("stage_full_casestudy_workspace"))
    if "full_prosa" in resume_config:
        options["full_prosa"] = bool(resume_config.get("full_prosa"))
    if "segmented_proof_workflow" in resume_config:
        options["segmented_proof_workflow"] = bool(resume_config.get("segmented_proof_workflow"))
    if "skill_enabled" in resume_config:
        options["enable_skill"] = bool(resume_config.get("skill_enabled"))
    if "trace_requests" in resume_config:
        options["trace_requests"] = bool(resume_config.get("trace_requests"))

    if options.get("model") is None:
        model = resume_config.get("model")
        if isinstance(model, str) and model:
            options["model"] = model

    if options.get("model_variant") is None:
        model_variant = resume_config.get("model_variant")
        if isinstance(model_variant, str) and model_variant:
            options["model_variant"] = model_variant

    full_prosa_source_dir = resume_config.get("full_prosa_source_dir")
    if isinstance(full_prosa_source_dir, str) and full_prosa_source_dir:
        options["full_prosa_source_dir"] = Path(full_prosa_source_dir)

    skill_source_dir = resume_config.get("skill_source_dir")
    if isinstance(skill_source_dir, str) and skill_source_dir:
        options["skill_source_dir"] = Path(skill_source_dir)


def _load_resume_workspace_state(
    base_run_dir: Path,
    workspace_name: str,
    existing_summary: dict | None = None,
) -> dict:
    run_dir = base_run_dir / workspace_name
    if not run_dir.is_dir():
        raise RuntimeError(f"Resume run directory does not contain workspace {workspace_name}: {run_dir}")

    result_payload = _read_json_payload(run_dir / "result.json")
    result = result_payload if isinstance(result_payload, dict) else (existing_summary or {})
    session_id = result.get("session_id") if isinstance(result, dict) else None
    session_id = session_id if isinstance(session_id, str) and session_id else None

    runtime_workspace = result.get("runtime_workspace_dir") if isinstance(result, dict) else None
    workspace_dir = Path(runtime_workspace) if isinstance(runtime_workspace, str) and runtime_workspace else run_dir / "workspace"
    if not workspace_dir.is_dir():
        raise RuntimeError(f"Resume workspace directory is missing for {workspace_name}: {workspace_dir}")

    xdg_data_home, session_available = _resolve_resume_xdg_data_home(
        base_run_dir=base_run_dir,
        workspace_name=workspace_name,
        session_id=session_id,
        result=result,
        existing_summary=existing_summary,
    )

    state = {
        "workspace_dir": str(workspace_dir),
        "result": result,
    }
    if xdg_data_home is not None:
        state["xdg_data_home"] = str(xdg_data_home)
    if session_id:
        state["session_available"] = session_available
    return state


def _merge_workspace_summaries(existing: list[dict], updated: list[dict]) -> list[dict]:
    updated_by_workspace = {
        entry["workspace"]: entry
        for entry in updated
        if isinstance(entry.get("workspace"), str)
    }
    merged: list[dict] = []
    seen: set[str] = set()

    for entry in existing:
        workspace = entry.get("workspace")
        if isinstance(workspace, str) and workspace in updated_by_workspace:
            merged.append(updated_by_workspace[workspace])
            seen.add(workspace)
        else:
            merged.append(entry)

    for workspace, entry in updated_by_workspace.items():
        if workspace not in seen:
            merged.append(entry)

    return merged


def recover_session_id_from_trace(
    env: dict[str, str],
    workspace_dir: Path,
    opencode_pid: int | None,
) -> str | None:
    """Recover the exact session ID from this invocation's XDG trace directory."""
    for run_dir in _trace_run_candidates(env, workspace_dir, opencode_pid):
        session_dirs = sorted(
            (path for path in run_dir.iterdir() if path.is_dir() and path.name.startswith("ses_")),
            key=lambda path: path.stat().st_mtime,
            reverse=True,
        )
        if session_dirs:
            return session_dirs[0].name

        summary = _read_json_file(run_dir / "summary.json")
        sessions = summary.get("sessions") if summary else None
        if isinstance(sessions, list) and sessions:
            last_session = sessions[-1]
            if isinstance(last_session, str) and last_session:
                return last_session

    return None


def _opencode_trace_root(env: dict[str, str]) -> Path:
    if env.get("OPENCODE_TRACE_DIR"):
        return Path(env["OPENCODE_TRACE_DIR"]).expanduser()
    xdg_data_home = Path(env.get("XDG_DATA_HOME", str(Path.home() / ".local" / "share")))
    return xdg_data_home / "opencode" / "trace"


def _trace_run_candidates(
    env: dict[str, str],
    workspace_dir: Path,
    opencode_pid: int | None,
) -> list[Path]:
    if opencode_pid is None:
        return []

    trace_root = _opencode_trace_root(env)
    if not trace_root.is_dir():
        return []

    candidates = sorted(
        trace_root.glob(f"run-*-{opencode_pid}"),
        key=lambda path: path.stat().st_mtime,
        reverse=True,
    )
    matched: list[Path] = []
    for run_dir in candidates:
        run_meta = _read_json_file(run_dir / "run.json")
        if run_meta:
            argv = run_meta.get("argv")
            if isinstance(argv, list):
                workspace_matches = any(
                    value == "--dir" and index + 1 < len(argv) and argv[index + 1] == str(workspace_dir)
                    for index, value in enumerate(argv)
                )
                if not workspace_matches:
                    continue
        matched.append(run_dir)
    return matched


def _copy_request_trace_for_attempt(
    *,
    env: dict[str, str],
    workspace_dir: Path,
    run_dir: Path,
    attempt: int,
    opencode_pid: int | None,
) -> dict | None:
    candidates = _trace_run_candidates(env, workspace_dir, opencode_pid)
    if not candidates:
        return None

    def request_record_count(trace_dir: Path) -> int:
        total = 0
        for request_log in trace_dir.rglob("requests.jsonl"):
            try:
                with request_log.open("r", encoding="utf-8", errors="ignore") as f:
                    total += sum(1 for line in f if line.strip())
            except OSError:
                continue
        return total

    source = candidates[0]
    destination_root = run_dir / "request_traces"
    try:
        source.relative_to(destination_root)
        return {
            "source": str(source),
            "destination": str(source),
            "request_jsonl_count": len(list(source.rglob("requests.jsonl"))),
            "request_record_count": request_record_count(source),
        }
    except ValueError:
        pass

    destination = destination_root / f"attempt_{attempt:02d}_{source.name}"
    destination_root.mkdir(parents=True, exist_ok=True)
    if destination.exists():
        shutil.rmtree(destination)
    shutil.copytree(source, destination)
    return {
        "source": str(source),
        "destination": str(destination),
        "request_jsonl_count": len(list(destination.rglob("requests.jsonl"))),
        "request_record_count": request_record_count(destination),
    }


# ---------------------------------------------------------------------------
# Single opencode invocation
# ---------------------------------------------------------------------------


def _opencode_startup_error_from_log(log_file: Path, offset: int) -> str | None:
    """Return a non-proof startup failure emitted during one invocation."""
    try:
        with log_file.open("rb") as f:
            f.seek(max(0, offset))
            delta = f.read().decode("utf-8", errors="replace")
    except OSError:
        return None

    if "ProviderModelNotFoundError" in delta:
        return "provider_model_not_found"
    return None


def _truncate_file_to_size(path: Path, size: int) -> None:
    """Discard stdout replay appended by an invocation that never started."""
    try:
        with path.open("r+b") as f:
            f.truncate(max(0, size))
    except FileNotFoundError:
        pass


def _invoke_opencode(
    cmd: list[str],
    *,
    env: dict[str, str],
    workspace_dir: Path,
    log_file: Path,
    json_log: Path,
    timeout_seconds: int,
    model_response_timeout_seconds: int = MODEL_RESPONSE_TIMEOUT_SECONDS,
    max_total_tokens: int | None = None,
    baseline_tokens: int = 0,
) -> tuple[int | None, bool, int | None, bool, bool]:
    """Run one opencode invocation.

    Returns (exit_code, timed_out, pid, token_limit_hit, model_response_timed_out).
    """

    def _step_finish_tokens_from_line(line: str) -> int:
        try:
            event = json.loads(line)
        except json.JSONDecodeError:
            return 0
        if not isinstance(event, dict) or event.get("type") != "step_finish":
            return 0
        part = event.get("part") if isinstance(event.get("part"), dict) else {}
        tokens = part.get("tokens") if isinstance(part.get("tokens"), dict) else {}
        step_total = tokens.get("total")
        if isinstance(step_total, (int, float)):
            return int(step_total)
        return int(tokens.get("input", 0)) + int(tokens.get("output", 0)) + int(tokens.get("reasoning", 0))

    timed_out = False
    token_limit_hit = False
    model_response_timed_out = False
    exit_code: int | None = None
    opencode_pid: int | None = None
    running_tokens = max(0, int(baseline_tokens))
    global _ACTIVE_OPENCODE_PROCESS
    try:
        with log_file.open("a") as lf, json_log.open("a") as jf:
            proc = subprocess.Popen(
                cmd,
                stdin=subprocess.DEVNULL,
                stdout=subprocess.PIPE,
                stderr=lf,
                env=env,
                cwd=str(workspace_dir),
                # The wrapper may spawn Bun, language servers, and proof
                # helpers. Keep the invocation in its own process group so a
                # timeout or runner shutdown cannot leave descendants alive.
                start_new_session=True,
                # Keep the supervisor lifecycle lock alive in the actual proof
                # process. If the Python runner is killed abruptly, a surviving
                # opencode/Bun process still prevents a duplicate experiment.
                pass_fds=inherited_run_lock_fds(),
            )
            _ACTIVE_OPENCODE_PROCESS = proc
            opencode_pid = proc.pid
            assert proc.stdout is not None

            # Reading stdout directly in this thread makes ``for raw_line in
            # proc.stdout`` an unbounded wait: a stalled streaming response
            # emits neither a line nor EOF, so the subsequent ``proc.wait``
            # timeout is never reached. Keep the pipe reader separate and let
            # this control loop enforce the invocation deadline.
            stdout_queue: queue.Queue[bytes | None] = queue.Queue()

            def _drain_stdout() -> None:
                try:
                    for raw_line in proc.stdout:
                        stdout_queue.put(raw_line)
                finally:
                    stdout_queue.put(None)

            stdout_thread = threading.Thread(target=_drain_stdout, daemon=True)
            stdout_thread.start()
            deadline = time.monotonic() + max(1, timeout_seconds)
            last_model_progress_at = time.monotonic()
            stdout_closed = False

            def _stop_process() -> None:
                _terminate_process_group(proc)

            try:
                while not stdout_closed:
                    now = time.monotonic()
                    remaining = deadline - now
                    model_wait_remaining = (
                        max(1, model_response_timeout_seconds)
                        - (now - last_model_progress_at)
                    )
                    if remaining <= 0:
                        timed_out = True
                        _stop_process()
                        break
                    if model_wait_remaining <= 0:
                        model_response_timed_out = True
                        _stop_process()
                        break
                    try:
                        raw_line = stdout_queue.get(
                            timeout=min(1.0, remaining, model_wait_remaining)
                        )
                    except queue.Empty:
                        continue
                    if raw_line is None:
                        stdout_closed = True
                        continue
                    line = raw_line.decode("utf-8", errors="replace")
                    jf.write(line)
                    jf.flush()
                    try:
                        event_type = json.loads(line).get("type")
                    except (json.JSONDecodeError, AttributeError):
                        event_type = None
                    # Parent sessions emit step_running heartbeats while a
                    # child LLM request is hung. Those heartbeats must not
                    # mask a missing model response.
                    if event_type != "step_running":
                        last_model_progress_at = time.monotonic()
                    if max_total_tokens is not None and max_total_tokens > 0:
                        running_tokens += _step_finish_tokens_from_line(line)
                        if running_tokens >= max_total_tokens:
                            token_limit_hit = True
                            _stop_process()
                            break
                if (
                    not token_limit_hit
                    and not timed_out
                    and not model_response_timed_out
                    and proc.poll() is None
                ):
                    remaining = deadline - time.monotonic()
                    if remaining <= 0:
                        timed_out = True
                        _stop_process()
                    else:
                        proc.wait(timeout=remaining)
            except subprocess.TimeoutExpired:
                _stop_process()
                timed_out = True
            finally:
                stdout_thread.join(timeout=1)
            exit_code = proc.returncode
    except Exception as exc:
        exit_code = -1
        try:
            with log_file.open("a") as lf:
                lf.write(f"runner failed to invoke opencode: {type(exc).__name__}: {exc}\n")
        except OSError:
            pass
    finally:
        _ACTIVE_OPENCODE_PROCESS = None
    return (
        exit_code,
        timed_out,
        opencode_pid,
        token_limit_hit,
        model_response_timed_out,
    )


# ---------------------------------------------------------------------------
# Run a single workspace (with retry loop)
# ---------------------------------------------------------------------------


def run_workspace(
    base_run_dir: Path,
    workspace_name: str,
    progress_file: Path,
    *,
    model: str | None = None,
    model_variant: str | None = None,
    run_timeout_seconds: int = 12 * 3600,
    model_response_timeout_seconds: int = MODEL_RESPONSE_TIMEOUT_SECONDS,
    max_total_tokens: int = MAX_TOTAL_TOKENS,
    max_retries: int = MAX_AGENT_RETRIES,
    opencode_bin: str = str(DEFAULT_OPENCODE_BIN),
    cases_root: Path | None = None,
    stage_full_casestudy_workspace: bool = False,
    full_prosa: bool = False,
    full_prosa_source_dir: Path = FULL_PROSA_SOURCE_ROOT,
    segmented_proof_workflow: bool = False,
    enable_skill: bool = False,
    skill_source_dir: Path = DEFAULT_SKILL_SOURCE_DIR,
    trace_requests: bool = False,
    extra_env: dict[str, str] | None = None,
    resume_state: dict | None = None,
) -> dict:
    source_dir = resolve_workspace_source_dir(workspace_name, cases_root)
    source_theorem_file = root_theorem_file(source_dir)

    run_dir = base_run_dir / workspace_name
    run_dir.mkdir(parents=True, exist_ok=True)

    resume_result = (resume_state or {}).get("result") if resume_state else None
    if resume_state:
        workspace_dir = Path(str(resume_state["workspace_dir"]))
        theorem_filename = resume_result.get("theorem_file") if isinstance(resume_result, dict) else None
        theorem_path = workspace_dir / theorem_filename if isinstance(theorem_filename, str) else None
        canonical_theorem_path = workspace_dir / source_theorem_file.name
        theorem_file = (
            theorem_path
            if theorem_path and theorem_path.is_file() and is_casestudy_theorem_file(theorem_path)
            else canonical_theorem_path
            if canonical_theorem_path.is_file()
            else root_theorem_file(workspace_dir)
        )
    else:
        workspace_dir, theorem_file = stage_workspace(
            source_dir,
            run_dir,
            stage_full_casestudy_workspace=stage_full_casestudy_workspace,
            full_prosa=full_prosa,
            full_prosa_source_dir=full_prosa_source_dir,
        )
    if enable_skill and not (workspace_dir / ".opencode" / "skill").is_dir():
        stage_workspace_skill(skill_source_dir, workspace_dir)
    theorem_name = target_theorem_name(source_theorem_file)
    theorem_statement = extract_target_theorem_statement(source_theorem_file)
    write_opencode_config(workspace_dir, theorem_file.name, enable_skill=enable_skill)

    prompt = build_prompt(
        theorem_file,
        theorem_name,
        theorem_statement,
        enable_skill=enable_skill,
        segmented_proof_workflow=segmented_proof_workflow,
    )
    prompt_file = run_dir / "prompt.md"
    write_text(prompt_file, prompt)

    preserve_retry_budget_on_resume = bool(
        resume_state and resume_state.get("preserve_retry_budget_on_resume")
    )
    latest_progress_attempt = (
        _latest_progress_attempt(progress_file, workspace_name)
        if resume_state and preserve_retry_budget_on_resume
        else None
    )

    prior_attempts = _int_value((resume_result or {}).get("attempts"))
    if latest_progress_attempt:
        prior_attempts = max(prior_attempts, _int_value(latest_progress_attempt.get("attempt")))
    prior_retries_used = _int_value((resume_result or {}).get("retries_used"), max(0, prior_attempts - 1))
    if latest_progress_attempt:
        prior_retries_used = max(
            prior_retries_used,
            _int_value(latest_progress_attempt.get("retries_used")),
        )
    prior_noop_recoveries = _int_value((resume_result or {}).get("noop_recoveries"))
    prior_model_attempts = _int_value(
        (resume_result or {}).get("model_attempts"),
        max(0, prior_attempts - prior_noop_recoveries),
    )
    if latest_progress_attempt:
        prior_model_attempts = max(
            prior_model_attempts,
            _int_value(latest_progress_attempt.get("model_attempts")),
        )
    reset_retries_on_resume = bool(
        resume_state and resume_state.get("reset_retries_on_resume")
    )
    if reset_retries_on_resume and preserve_retry_budget_on_resume:
        raise RuntimeError(
            "Resume retry budget options conflict: cannot reset and preserve the active retry epoch together."
        )
    if preserve_retry_budget_on_resume:
        result_has_retry_epoch = isinstance(resume_result, dict) and all(
            key in resume_result
            for key in ("retry_budget_model_attempts", "retry_budget_retries_used")
        )
        progress_has_retry_epoch = bool(latest_progress_attempt) and all(
            key in latest_progress_attempt
            for key in ("retry_budget_model_attempts", "retry_budget_retries_used")
        )
        if not result_has_retry_epoch and not progress_has_retry_epoch:
            raise RuntimeError(
                "Cannot preserve retry budget: neither result.json nor progress.jsonl has active retry-epoch counters for this workspace."
            )
        retry_budget_prior_model_attempts = max(
            _int_value((resume_result or {}).get("retry_budget_model_attempts")),
            _int_value((latest_progress_attempt or {}).get("retry_budget_model_attempts")),
        )
        retry_budget_prior_retries_used = max(
            _int_value((resume_result or {}).get("retry_budget_retries_used")),
            _int_value((latest_progress_attempt or {}).get("retry_budget_retries_used")),
        )
    else:
        retry_budget_prior_model_attempts = (
            0 if reset_retries_on_resume else prior_model_attempts
        )
        retry_budget_prior_retries_used = (
            0 if reset_retries_on_resume else prior_retries_used
        )
    prior_total_tokens = _int_value((resume_result or {}).get("total_tokens"))
    if latest_progress_attempt:
        prior_total_tokens = max(
            prior_total_tokens,
            _int_value(latest_progress_attempt.get("cumulative_tokens")),
        )
    request_trace_tokens = (
        extract_request_trace_tokens(run_dir / "request_traces" / "requests.jsonl")
        if resume_state
        else 0
    )
    prior_total_tokens = max(prior_total_tokens, request_trace_tokens)
    prior_elapsed_seconds = _float_value((resume_result or {}).get("elapsed_seconds"))
    prior_status = (resume_result or {}).get("status")
    prior_session_id = (resume_result or {}).get("session_id")
    prior_session_id = prior_session_id if isinstance(prior_session_id, str) and prior_session_id else None
    # Resume metadata can come from different summary/result sources; fall back to
    # the explicit resume state payload to avoid losing the reusable session id.
    if prior_session_id is None and resume_state:
        resume_payload = resume_state.get("result") if isinstance(resume_state, dict) else None
        candidate_session = resume_payload.get("session_id") if isinstance(resume_payload, dict) else None
        if isinstance(candidate_session, str) and candidate_session:
            prior_session_id = candidate_session
    resume_session_available = bool((resume_state or {}).get("session_available")) if resume_state else True
    if resume_state and prior_session_id and not resume_session_available:
        prior_session_id = None

    summary: dict = {
        "workspace": workspace_name,
        "source_theorem_file": str(source_theorem_file),
        "runtime_workspace_dir": str(workspace_dir),
        "theorem_file": theorem_file.name,
        "theorem_name": theorem_name,
        "model": model,
        "model_variant": model_variant,
        "prosa_mode": "full" if full_prosa else "minimal",
        "prosa_source_dir": str(full_prosa_source_dir if full_prosa else PROSA_SOURCE_ROOT),
        "skill_enabled": enable_skill,
        "skill_source_dir": str(skill_source_dir) if enable_skill else None,
        "trace_requests": trace_requests,
        "started_at": now_iso(),
        "status": "running",
        "resumed": bool(resume_state),
    }
    if resume_state:
        summary["resume_run_dir"] = str(base_run_dir)
        summary["resumed_from_status"] = prior_status
        summary["resumed_from_attempts"] = prior_attempts
        summary["resumed_from_total_tokens"] = prior_total_tokens
        if request_trace_tokens:
            summary["resumed_from_request_trace_tokens"] = request_trace_tokens
        if resume_state.get("xdg_data_home"):
            summary["resume_xdg_data_home"] = resume_state["xdg_data_home"]
        summary["resume_session_strategy"] = "reuse_session" if prior_session_id else "new_session"
        if reset_retries_on_resume:
            summary["retry_budget_reset_on_resume"] = True
            summary["historical_model_attempts"] = prior_model_attempts
            summary["historical_retries_used"] = prior_retries_used
        if preserve_retry_budget_on_resume:
            summary["retry_budget_preserved_on_resume"] = True
            summary["preserved_retry_budget_model_attempts"] = retry_budget_prior_model_attempts
            summary["preserved_retry_budget_retries_used"] = retry_budget_prior_retries_used
    write_json(run_dir / "plan.json", summary)
    append_jsonl(progress_file, {"event": "resume_start" if resume_state else "start", **summary})

    env = workspace_coq_environment(workspace_dir)
    if extra_env:
        env.update(extra_env)
    service_tier_applied, service_tier_warning = _inject_openrouter_service_tier_config(
        env,
        model=model or env.get("OPENCODE_MODEL"),
        service_tier=env.get("OPENCODE_SERVICE_TIER"),
    )
    if service_tier_warning:
        append_jsonl(
            progress_file,
            {
                "event": "service_tier_warning",
                "workspace": workspace_name,
                "warning": service_tier_warning,
            },
        )
    if resume_state and resume_state.get("xdg_data_home"):
        _apply_xdg_data_home(env, Path(str(resume_state["xdg_data_home"])))
    env["OPENCODE_STRICT_WORKSPACE_BOUNDARY"] = "1"
    if trace_requests:
        env["OPENCODE_TRACE_DIR"] = str(run_dir / "request_traces")
        summary["request_trace_root"] = env["OPENCODE_TRACE_DIR"]

    requested_service_tier = (env.get("OPENCODE_SERVICE_TIER") or "").strip()
    if requested_service_tier:
        summary["requested_service_tier"] = requested_service_tier
        summary["service_tier_applied"] = service_tier_applied

    preflight = toolchain_preflight(workspace_dir, theorem_file, env, opencode_bin)
    summary["toolchain_preflight"] = preflight
    write_json(run_dir / "toolchain_manifest.json", preflight)
    append_jsonl(
        progress_file,
        {
            "event": "toolchain_preflight",
            "workspace": workspace_name,
            **preflight,
        },
    )
    if not preflight.get("ok"):
        summary["status"] = "error"
        summary["error"] = (
            "toolchain preflight failed before model execution: "
            + str(preflight.get("error") or preflight.get("failure_kind") or "unknown failure")
        )
        summary["finished_at"] = now_iso()
        summary["total_tokens"] = prior_total_tokens
        write_json(run_dir / "plan.json", summary)
        write_json(run_dir / "result.json", summary)
        append_jsonl(progress_file, {"event": "finish", **summary})
        return summary
    write_json(run_dir / "plan.json", summary)

    log_file = run_dir / "opencode.log"
    json_log = run_dir / "opencode_events.jsonl"
    proof_runtime_state = extract_proof_runtime_state(json_log, 0, theorem_file)
    resume_history_compaction = ""
    if resume_state and resume_state.get("fresh_session_on_resume"):
        resume_history_compaction = _compact_resume_history(json_log)
        if resume_history_compaction:
            summary["history_compaction_chars"] = len(resume_history_compaction)
            write_json(run_dir / "plan.json", summary)
        for path in (log_file, json_log):
            _archive_fresh_resume_log(path)

    initial_trace_tokens = extract_trace_usage(json_log)[1]
    trace_token_offset = max(0, prior_total_tokens - initial_trace_tokens)

    t0 = time.time()
    cumulative_tokens = trace_token_offset + initial_trace_tokens
    session_id: str | None = prior_session_id
    attempt = 0
    total_attempts = prior_attempts
    productive_attempts = 0
    noop_retry_charges = 0
    noop_recoveries = 0
    reasoning_output_exhaustion_recoveries = 0
    consecutive_reasoning_output_exhaustions = 0
    model_response_timeout_recoveries = 0
    consecutive_model_response_timeouts = 0
    consecutive_noop_recoveries = 0
    noop_session_id: str | None = None
    noop_session_streak = 0
    consecutive_unchanged_productive_attempts = 0
    stalled_session_recoveries = 0
    missing_skeleton_recoveries = 0
    missing_skeleton_session_id: str | None = None
    missing_skeleton_session_streak = 0
    force_fresh_session = False
    last_failure_info: dict | None = None
    spec_violation_detected = False
    spec_violation_info: dict | None = None
    last_preserved_skeleton_fingerprint: str | None = None
    last_preserved_progress_fingerprint: str | None = None
    unchanged_fingerprint_counts: dict[str, int] = {}
    semantic_livelock_handoffs: set[str] = set()

    def retry_budget_model_attempts() -> int:
        return (
            retry_budget_prior_model_attempts
            + productive_attempts
            + noop_retry_charges
        )

    def retry_budget_retries_used() -> int:
        current_budget_attempts = productive_attempts + noop_retry_charges
        if reset_retries_on_resume:
            return max(0, current_budget_attempts - 1)
        return retry_budget_prior_retries_used + max(
            0,
            current_budget_attempts - (0 if resume_state else 1),
        )

    def theorem_file_fingerprint() -> str:
        try:
            payload = theorem_file.read_bytes()
        except OSError:
            return ""
        return hashlib.sha256(payload).hexdigest()

    def theorem_progress_fingerprint(file_fingerprint: str | None = None) -> str:
        return proof_runtime_fingerprint(
            file_fingerprint if file_fingerprint is not None else theorem_file_fingerprint(),
            proof_runtime_state,
        )

    current_success, current_proof_info = check_proof_success(source_theorem_file, workspace_dir, theorem_file)
    if current_proof_info.get("unauthorized_modification") or current_proof_info.get("integrity_check_failed"):
        spec_violation_detected = True
        spec_violation_info = dict(current_proof_info)
    if current_success:
        summary["status"] = "success"
        summary.update(current_proof_info)
    else:
        last_failure_info = current_proof_info

    while summary.get("status") == "running":
        attempt += 1
        total_attempts = prior_attempts + attempt
        remaining_seconds = max(60, run_timeout_seconds - int(time.time() - t0))

        if productive_attempts == 0 and noop_retry_charges == 0 and not resume_state:
            cmd = [opencode_bin, "run"]
            if model:
                cmd.extend(["--model", model])
            if model_variant:
                cmd.extend(["--variant", model_variant])
            cmd.extend(["--dir", str(workspace_dir)])
            cmd.extend(["--format", "json"])
            if trace_requests:
                cmd.append("--trace-requests")
            cmd.append(prompt)
        else:
            continuation_prompt = build_continuation_prompt(
                theorem_file,
                theorem_name,
                theorem_statement,
                proof_info=last_failure_info,
                # Raw invocations include no-op recovery launches and can grow
                # well past the productive proof budget.  Report the model-work
                # count so the prompt never says e.g. "retry 24 of 16".
                retry_index=retry_budget_model_attempts(),
                max_retries=max_retries,
                enable_skill=enable_skill,
                segmented_proof_workflow=segmented_proof_workflow,
                history_compaction=resume_history_compaction,
            )
            cmd = [opencode_bin, "run"]
            if model:
                cmd.extend(["--model", model])
            if model_variant:
                cmd.extend(["--variant", model_variant])
            cmd.extend(["--dir", str(workspace_dir)])
            cmd.extend(["--format", "json"])
            if trace_requests:
                cmd.append("--trace-requests")
            if session_id and not force_fresh_session:
                cmd.extend(["--session", session_id])
            elif not force_fresh_session and (not resume_state or attempt > 1):
                cmd.append("--continue")
            cmd.append(continuation_prompt)

        if force_fresh_session:
            session_strategy = "fresh_session_recovery"
        elif session_id:
            session_strategy = "reuse_session"
        elif "--continue" in cmd:
            session_strategy = "continue_latest"
        else:
            session_strategy = "new_session"

        append_jsonl(progress_file, {
            "event": "attempt",
            "workspace": workspace_name,
            "attempt": total_attempts,
            "resume_attempt": attempt,
            "previous_attempts": prior_attempts,
            "cumulative_tokens": cumulative_tokens,
            "total_tokens": cumulative_tokens,
            "session_id": session_id,
            "session_strategy": session_strategy,
            "xdg_data_home": env.get("XDG_DATA_HOME"),
            "model_attempts": (
                prior_model_attempts + productive_attempts + noop_retry_charges
            ),
            "noop_recoveries": prior_noop_recoveries + noop_recoveries,
            "retries_used": prior_retries_used
            + max(
                0,
                productive_attempts
                - (1 if reset_retries_on_resume else (0 if resume_state else 1)),
            ),
            "retry_budget_model_attempts": retry_budget_model_attempts(),
            "retry_budget_retries_used": retry_budget_retries_used(),
            "retry_budget_max_retries": max_retries,
        })

        pre_attempt_tokens = cumulative_tokens
        pre_trace_usage = extract_trace_usage(json_log)
        pre_trace_tokens = pre_trace_usage[1]
        pre_trace_steps = pre_trace_usage[2]
        invoked_session_id = session_id
        pre_json_size = json_log.stat().st_size if json_log.exists() else 0
        request_trace_file = run_dir / "request_traces" / "requests.jsonl"
        pre_request_trace_size = (
            request_trace_file.stat().st_size
            if trace_requests and request_trace_file.exists()
            else 0
        )
        pre_log_size = log_file.stat().st_size if log_file.exists() else 0
        pre_theorem_fingerprint = theorem_file_fingerprint()
        pre_progress_fingerprint = theorem_progress_fingerprint(pre_theorem_fingerprint)

        (
            exit_code,
            timed_out,
            opencode_pid,
            token_limit_hit,
            model_response_timed_out,
        ) = _invoke_opencode(
            cmd,
            env=env,
            workspace_dir=workspace_dir,
            log_file=log_file,
            json_log=json_log,
            timeout_seconds=remaining_seconds,
            model_response_timeout_seconds=model_response_timeout_seconds,
            max_total_tokens=max_total_tokens,
            baseline_tokens=pre_attempt_tokens,
        )

        startup_error = _opencode_startup_error_from_log(log_file, pre_log_size)
        if startup_error:
            # `opencode --continue` can replay old JSON events to stdout before
            # discovering that its provider is unavailable. Those records are
            # not new model work and must not consume tokens or proof retries.
            _truncate_file_to_size(json_log, pre_json_size)

        found_session, observed_total_tokens, observed_model_steps = extract_trace_usage(json_log)
        proof_runtime_state = merge_proof_runtime_state(
            proof_runtime_state,
            extract_proof_runtime_state(json_log, pre_json_size, theorem_file),
        )
        attempt_tokens = max(0, observed_total_tokens - pre_trace_tokens)
        attempt_model_steps = max(0, observed_model_steps - pre_trace_steps)
        model_work_observed = attempt_tokens > 0 or attempt_model_steps > 0
        attempt_tool_calls = extract_attempt_tool_calls(json_log, pre_json_size)
        attempt_terminal_text = extract_attempt_terminal_text(json_log, pre_json_size)
        attempt_request_outcome = (
            extract_attempt_request_outcome(
                request_trace_file,
                pre_request_trace_size,
            )
            if trace_requests
            else {
                "request_count": 0,
                "finish_reasons": [],
                "length_terminated_count": 0,
                "output_tokens": 0,
                "reasoning_tokens": 0,
                "reasoning_fraction": 0.0,
                "reasoning_output_exhausted": False,
            }
        )
        materialization_livelock = extract_materialization_livelock(attempt_terminal_text)
        decomposition_terminal = (
            extract_attempt_decomposition_terminal(json_log, pre_json_size)
            if decomposition_terminal_receipts_enabled(
                segmented_proof_workflow=segmented_proof_workflow,
                env=env,
            )
            else None
        )
        terminal_text_lower = attempt_terminal_text.lower()
        terminal_stall_markers = (
            "semantic revision is exhausted",
            "semantic revision was exhausted",
            "single permitted semantic revision",
            "must not call `proof_plan` again",
            "must not call proof_plan again",
            "active decomposition constraints",
            "exhausted decomposition constraints",
            "exhausted-decomposition",
        )
        terminal_stall_detected = any(
            marker in terminal_text_lower for marker in terminal_stall_markers
        )
        post_theorem_fingerprint = theorem_file_fingerprint()
        post_progress_fingerprint = theorem_progress_fingerprint(post_theorem_fingerprint)
        model_terminal_noop = (
            model_work_observed
            and pre_progress_fingerprint == post_progress_fingerprint
            and (attempt_tool_calls == 0 or terminal_stall_detected)
        )
        reasoning_output_exhausted = bool(
            model_terminal_noop
            and attempt_tool_calls == 0
            and not attempt_terminal_text.strip()
            and attempt_request_outcome.get("reasoning_output_exhausted")
        )
        cumulative_tokens += attempt_tokens
        if found_session:
            session_id = found_session
            invoked_session_id = found_session
        elif session_id is None:
            recovered_session = recover_session_id_from_trace(env, workspace_dir, opencode_pid)
            if recovered_session:
                session_id = recovered_session
                invoked_session_id = recovered_session

        # A source-bound proof-plan terminal verdict is real model work even
        # when it leaves the theorem/runtime fingerprint unchanged.  Count it
        # against the normal proof retry budget before choosing same-session
        # or fresh-session recovery.
        if (
            model_work_observed
            and not model_response_timed_out
            and materialization_livelock is None
            and (not model_terminal_noop or decomposition_terminal is not None)
        ):
            productive_attempts += 1
            consecutive_noop_recoveries = 0
            consecutive_reasoning_output_exhaustions = 0
            noop_session_id = None
            noop_session_streak = 0
            force_fresh_session = False

        if not model_response_timed_out:
            consecutive_model_response_timeouts = 0

        if startup_error:
            summary["status"] = "error"
            summary["error"] = (
                "opencode failed before model execution: requested provider/model was not available"
            )
            summary["startup_error"] = startup_error
            if exit_code is not None:
                summary["exit_code"] = exit_code
            append_jsonl(progress_file, {
                "event": "opencode_startup_error",
                "workspace": workspace_name,
                "attempt": total_attempts,
                "startup_error": startup_error,
                "retries_preserved": True,
            })
            break

        if trace_requests:
            trace_copy = _copy_request_trace_for_attempt(
                env=env,
                workspace_dir=workspace_dir,
                run_dir=run_dir,
                attempt=total_attempts,
                opencode_pid=opencode_pid,
            )
            if trace_copy:
                summary.setdefault("request_trace_dirs", []).append(trace_copy["destination"])
                summary["request_trace_record_count"] = int(summary.get("request_trace_record_count", 0)) + int(
                    trace_copy.get("request_record_count", 0)
                )
                append_jsonl(progress_file, {
                    "event": "request_trace_copied",
                    "workspace": workspace_name,
                    "attempt": total_attempts,
                    **trace_copy,
                })

        if token_limit_hit:
            summary["status"] = "token_limit"
            summary["token_limit_realtime_kill"] = True
            summary["token_limit_threshold"] = max_total_tokens
            break

        # Check stop conditions
        success, proof_info = check_proof_success(source_theorem_file, workspace_dir, theorem_file)
        if proof_info.get("unauthorized_modification") or proof_info.get("integrity_check_failed"):
            if not spec_violation_detected:
                append_jsonl(progress_file, {
                    "event": "spec_violation_detected",
                    "workspace": workspace_name,
                    "attempt": total_attempts,
                    "issues": proof_info.get("integrity_issues", []),
                })
            spec_violation_detected = True
            spec_violation_info = dict(proof_info)

        if success:
            summary["status"] = "success"
            summary.update(proof_info)
            break

        if materialization_livelock:
            last_failure_info = {
                **proof_info,
                "materialization_livelock": materialization_livelock,
            }
            session_id = None
            force_fresh_session = True
            append_jsonl(progress_file, {
                "event": "materialization_livelock_recovery",
                "workspace": workspace_name,
                "attempt": total_attempts,
                "receipt": materialization_livelock,
                "recovery": "force_fresh_session",
                "retries_preserved": True,
            })
            print(
                f"  [{workspace_name}] accepted-plan materialization repeated without "
                "hard progress; starting a fresh compact proof session..."
            )
            time.sleep(2)
            continue

        if decomposition_terminal:
            terminal_source_hash = str(decomposition_terminal.get("source_hash") or "")
            current_source_hash = theorem_file_fingerprint()
            if terminal_source_hash in proof_runtime_source_hashes(
                current_source_hash,
                proof_runtime_state,
            ):
                recovery_strategy = decomposition_terminal_recovery_strategy(
                    decomposition_terminal,
                    retry_budget_model_attempts(),
                    max_retries,
                )
                if recovery_strategy == "retry_limit":
                    summary["status"] = "retry_limit"
                    summary["decomposition_terminal_verdict"] = decomposition_terminal
                    summary.update(proof_info)
                    append_jsonl(progress_file, {
                        "event": "decomposition_plan_generation_recovery_blocked",
                        "workspace": workspace_name,
                        "attempt": total_attempts,
                        "source_hash": current_source_hash,
                        "reason": "proof_retry_limit_reached",
                        "retry_budget_model_attempts": retry_budget_model_attempts(),
                        "retry_budget_max_retries": max_retries,
                    })
                    break
                if recovery_strategy == "retry_same_session":
                    last_failure_info = {
                        **proof_info,
                        "decomposition_plan_generation_recovery": {
                            "planning_generation": decomposition_terminal.get("planning_generation", 0),
                            "failure_fingerprint": decomposition_terminal.get("failure_fingerprint"),
                            "best_semantic_fingerprint": decomposition_terminal.get("best_semantic_fingerprint"),
                            "blockers": decomposition_terminal.get("blockers", []),
                        },
                    }
                    force_fresh_session = False
                    append_jsonl(progress_file, {
                        "event": "decomposition_plan_generation_recovery",
                        "workspace": workspace_name,
                        "attempt": total_attempts,
                        "session_id": session_id,
                        "source_hash": current_source_hash,
                        "planning_generation": decomposition_terminal.get("planning_generation", 0),
                        "failure_fingerprint": decomposition_terminal.get("failure_fingerprint"),
                        "best_semantic_fingerprint": decomposition_terminal.get("best_semantic_fingerprint"),
                        "blockers": decomposition_terminal.get("blockers", []),
                        "recovery": "retry_same_session",
                        "retry_consumed": True,
                    })
                    print(
                        f"  [{workspace_name}] proof-plan generation exhausted; "
                        "continuing the authorized recovery generation in the same session..."
                    )
                    time.sleep(2)
                    continue

                last_failure_info = {
                    **proof_info,
                    "decomposition_terminal_fresh_attempt": {
                        "planning_generation": decomposition_terminal.get("planning_generation", 0),
                        "failure_fingerprint": decomposition_terminal.get("failure_fingerprint"),
                        "best_semantic_fingerprint": decomposition_terminal.get("best_semantic_fingerprint"),
                        "semantic_fingerprint": decomposition_terminal.get("semantic_fingerprint"),
                        "blockers": decomposition_terminal.get("blockers", []),
                    },
                }
                session_id = None
                force_fresh_session = True
                append_jsonl(progress_file, {
                    "event": "decomposition_terminal_fresh_attempt",
                    "workspace": workspace_name,
                    "attempt": total_attempts,
                    "source_hash": current_source_hash,
                    "planning_generation": decomposition_terminal.get("planning_generation", 0),
                    "failure_fingerprint": decomposition_terminal.get("failure_fingerprint"),
                    "best_semantic_fingerprint": decomposition_terminal.get("best_semantic_fingerprint"),
                    "semantic_fingerprint": decomposition_terminal.get("semantic_fingerprint"),
                    "blockers": decomposition_terminal.get("blockers", []),
                    "recovery": "force_fresh_session",
                    "retry_consumed": True,
                })
                print(
                    f"  [{workspace_name}] proof-plan recovery generations exhausted; "
                    "starting a fresh proof session with the current workspace..."
                )
                time.sleep(2)
                continue

        if model_response_timed_out:
            model_response_timeout_recoveries += 1
            consecutive_model_response_timeouts += 1
            # Reuse the exact session once so the model retains its proof
            # context. If the same session stalls again, switch to a fresh
            # continuation session while keeping the workspace unchanged.
            use_fresh_session = consecutive_model_response_timeouts >= 2
            if use_fresh_session:
                session_id = None
                force_fresh_session = True
                consecutive_model_response_timeouts = 0
            last_failure_info = proof_info
            append_jsonl(progress_file, {
                "event": "model_response_timeout_recovery",
                "workspace": workspace_name,
                "attempt": total_attempts,
                "session_id": invoked_session_id,
                "session_strategy": session_strategy,
                "timeout_seconds": model_response_timeout_seconds,
                "attempt_tokens": attempt_tokens,
                "attempt_model_steps": attempt_model_steps,
                "cumulative_tokens": cumulative_tokens,
                "retries_preserved": True,
                "recovery": (
                    "force_fresh_session" if use_fresh_session else "retry_same_session"
                ),
            })
            print(
                f"  [{workspace_name}] model response silent for "
                f"{model_response_timeout_seconds}s; retrying without consuming "
                "a proof retry..."
            )
            time.sleep(2)
            continue

        if timed_out or (time.time() - t0) >= run_timeout_seconds:
            summary["status"] = "timeout"
            summary.update(proof_info)
            break

        if cumulative_tokens >= max_total_tokens:
            summary["status"] = "token_limit"
            summary.update(proof_info)
            break

        if exit_code is not None and exit_code < 0:
            summary["status"] = "error"
            summary["exit_code"] = exit_code
            summary.update(proof_info)
            break

        if not model_work_observed or model_terminal_noop:
            noop_recoveries += 1
            consecutive_noop_recoveries += 1
            if reasoning_output_exhausted:
                reasoning_output_exhaustion_recoveries += 1
                consecutive_reasoning_output_exhaustions += 1
            else:
                consecutive_reasoning_output_exhaustions = 0
            noop_session_id, noop_session_streak, use_fresh_session = (
                _same_session_retry_or_fresh(
                    invoked_session_id,
                    noop_session_id,
                    noop_session_streak,
                )
            )
            noop_streak = consecutive_noop_recoveries
            charge_retry = _should_charge_noop_recovery(noop_streak)
            if charge_retry:
                noop_retry_charges += 1
                use_fresh_session = True

            recovery_kind = (
                "force_fresh_session_retry_charged"
                if charge_retry
                else "force_fresh_session"
                if use_fresh_session
                else "retry_same_session"
            )
            append_jsonl(progress_file, {
                "event": (
                    "reasoning_output_exhausted_recovery"
                    if reasoning_output_exhausted
                    else "model_terminal_noop_recovery"
                    if model_terminal_noop
                    else "noop_retry_recovery"
                ),
                "workspace": workspace_name,
                "attempt": total_attempts,
                "session_id": invoked_session_id,
                "session_strategy": session_strategy,
                "attempt_tokens": attempt_tokens,
                "attempt_model_steps": attempt_model_steps,
                "attempt_tool_calls": attempt_tool_calls,
                "terminal_stall_detected": terminal_stall_detected,
                "theorem_unchanged": pre_theorem_fingerprint == post_theorem_fingerprint,
                "cumulative_tokens": cumulative_tokens,
                "consecutive_noop_recoveries": noop_streak,
                "reasoning_output_exhausted": reasoning_output_exhausted,
                "consecutive_reasoning_output_exhaustions": (
                    consecutive_reasoning_output_exhaustions
                ),
                "request_outcome": attempt_request_outcome,
                "noop_session_streak": noop_session_streak,
                "recovery": recovery_kind,
                "retry_charged": charge_retry,
                "retries_preserved": not charge_retry,
            })

            if reasoning_output_exhausted:
                last_failure_info = {
                    **proof_info,
                    "reasoning_output_exhausted_recovery": {
                        "consecutive_exhaustions": (
                            consecutive_reasoning_output_exhaustions
                        ),
                        "request_outcome": attempt_request_outcome,
                        "retry_charged": charge_retry,
                    },
                }
            else:
                last_failure_info = proof_info

            if charge_retry:
                append_jsonl(progress_file, {
                    "event": "noop_recovery_budget_charged",
                    "workspace": workspace_name,
                    "attempt": total_attempts,
                    "consecutive_noop_recoveries": noop_streak,
                    "reasoning_output_exhausted": reasoning_output_exhausted,
                    "noop_retry_charges": noop_retry_charges,
                    "retry_budget_model_attempts": retry_budget_model_attempts(),
                    "retry_budget_retries_used": retry_budget_retries_used(),
                    "retry_budget_max_retries": max_retries,
                    "recovery": "fresh_compact_handoff",
                })
                consecutive_noop_recoveries = 0
                consecutive_reasoning_output_exhaustions = 0
                noop_session_id = None
                noop_session_streak = 0

                if retry_budget_model_attempts() >= max_retries + 1:
                    summary["status"] = "retry_limit"
                    summary.update(proof_info)
                    break

            if use_fresh_session:
                session_id = None
                force_fresh_session = True
            else:
                force_fresh_session = False
            print(
                f"  [{workspace_name}] attempt {total_attempts} produced no tool/file activity; "
                + (
                    "charging one proof retry and forcing a fresh compact handoff"
                    if charge_retry
                    else "forcing a fresh session"
                    if use_fresh_session
                    else "retrying the same session once"
                )
                + (
                    "..."
                    if charge_retry
                    else " without consuming a proof retry..."
                )
            )
            time.sleep(2)
            continue

        if proof_info.get("has_forbidden_shortcut"):
            if (
                segmented_proof_workflow
                and productive_attempts == 1
                and _preserve_first_attempt_admit_skeleton(proof_info)
            ):
                proof_info["admit_skeleton_retained"] = True
                last_preserved_skeleton_fingerprint = theorem_file_fingerprint()
                last_preserved_progress_fingerprint = theorem_progress_fingerprint(
                    last_preserved_skeleton_fingerprint
                )
                unchanged_fingerprint_counts[last_preserved_progress_fingerprint] = (
                    unchanged_fingerprint_counts.get(last_preserved_progress_fingerprint, 0) + 1
                )
                append_jsonl(progress_file, {
                    "event": "admit_skeleton_retained",
                    "workspace": workspace_name,
                    "attempt": total_attempts,
                    "file_fingerprint": last_preserved_skeleton_fingerprint,
                    "progress_fingerprint": last_preserved_progress_fingerprint,
                    "retained_shortcuts": [
                        name
                        for name in ("Admitted", "admit")
                        if proof_info.get(f"has_{name.lower()}")
                    ],
                })
                last_failure_info = proof_info
                print(
                    f"  [{workspace_name}] attempt {total_attempts} retained first-attempt admit skeleton, "
                    f"tokens={cumulative_tokens:,}, retry={retry_budget_retries_used()}/{max_retries}, continuing..."
                )
                time.sleep(2)
                continue

            cleanup_info = cleanup_forbidden_shortcuts(
                source_theorem_file,
                theorem_file,
                preserve_segmented_skeleton=segmented_proof_workflow,
            )
            proof_info.update(cleanup_info)
            if cleanup_info.get("segmented_skeleton_preserved"):
                proof_info["admit_skeleton_retained"] = True
                current_skeleton_fingerprint = theorem_file_fingerprint()
                current_progress_fingerprint = theorem_progress_fingerprint(
                    current_skeleton_fingerprint
                )
                append_jsonl(progress_file, {
                    "event": "admit_skeleton_retained",
                    "workspace": workspace_name,
                    "attempt": total_attempts,
                    "reason": "segmented_proof_region_skeleton",
                    "file_fingerprint": current_skeleton_fingerprint,
                    "progress_fingerprint": current_progress_fingerprint,
                })

                if (
                    last_preserved_progress_fingerprint is not None
                    and current_progress_fingerprint == last_preserved_progress_fingerprint
                ):
                    consecutive_unchanged_productive_attempts += 1
                    stalled_session = (
                        consecutive_unchanged_productive_attempts
                        >= MAX_CONSECUTIVE_UNCHANGED_PRODUCTIVE_ATTEMPTS
                    )
                    append_jsonl(progress_file, {
                        "event": "unchanged_theorem_after_model_work",
                        "workspace": workspace_name,
                        "attempt": total_attempts,
                        "attempt_tokens": attempt_tokens,
                        "attempt_model_steps": attempt_model_steps,
                        "file_fingerprint": current_skeleton_fingerprint,
                        "progress_fingerprint": current_progress_fingerprint,
                        "consecutive_unchanged_productive_attempts": (
                            consecutive_unchanged_productive_attempts
                        ),
                        "action": (
                            "force_fresh_session"
                            if stalled_session
                            else "continue_until_verified_limit"
                        ),
                    })
                else:
                    consecutive_unchanged_productive_attempts = 0

                identical_fingerprint_attempts = unchanged_fingerprint_counts.get(
                    current_progress_fingerprint, 0
                ) + 1
                unchanged_fingerprint_counts[current_progress_fingerprint] = (
                    identical_fingerprint_attempts
                )
                last_preserved_skeleton_fingerprint = current_skeleton_fingerprint
                last_preserved_progress_fingerprint = current_progress_fingerprint

                if (
                    identical_fingerprint_attempts
                    >= MAX_IDENTICAL_THEOREM_FINGERPRINT_ATTEMPTS
                ):
                    if current_progress_fingerprint not in semantic_livelock_handoffs:
                        semantic_livelock_handoffs.add(current_progress_fingerprint)
                        last_failure_info = {
                            **proof_info,
                            "semantic_livelock_recovery": {
                                "file_fingerprint": current_skeleton_fingerprint,
                                "progress_fingerprint": current_progress_fingerprint,
                                "identical_attempts": identical_fingerprint_attempts,
                            },
                        }
                        append_jsonl(progress_file, {
                            "event": "semantic_livelock_route_remodel_handoff",
                            "workspace": workspace_name,
                            "attempt": total_attempts,
                            "file_fingerprint": current_skeleton_fingerprint,
                            "progress_fingerprint": current_progress_fingerprint,
                            "identical_attempts": identical_fingerprint_attempts,
                            "limit": MAX_IDENTICAL_THEOREM_FINGERPRINT_ATTEMPTS,
                            "recovery": "fresh_route_remodel_session",
                        })
                        session_id = None
                        force_fresh_session = True
                        consecutive_unchanged_productive_attempts = 0
                        print(
                            f"  [{workspace_name}] theorem source remained identical for "
                            f"{identical_fingerprint_attempts} productive attempts; forcing one "
                            "fresh route-remodel handoff instead of another ordinary continuation..."
                        )
                        time.sleep(2)
                        continue

                    summary["status"] = "semantic_livelock"
                    summary["semantic_livelock"] = {
                        "file_fingerprint": current_skeleton_fingerprint,
                        "progress_fingerprint": current_progress_fingerprint,
                        "identical_attempts": identical_fingerprint_attempts,
                        "route_remodel_handoff_exhausted": True,
                    }
                    summary.update(proof_info)
                    append_jsonl(progress_file, {
                        "event": "semantic_livelock_terminal",
                        "workspace": workspace_name,
                        "attempt": total_attempts,
                        "file_fingerprint": current_skeleton_fingerprint,
                        "progress_fingerprint": current_progress_fingerprint,
                        "identical_attempts": identical_fingerprint_attempts,
                        "reason": "fresh route-remodel handoff produced no theorem source change",
                    })
                    break

                if retry_budget_model_attempts() >= max_retries + 1:
                    summary["status"] = "retry_limit"
                    if exit_code is not None:
                        summary["exit_code"] = exit_code
                    summary.update(proof_info)
                    break

                if (
                    consecutive_unchanged_productive_attempts
                    >= MAX_CONSECUTIVE_UNCHANGED_PRODUCTIVE_ATTEMPTS
                ):
                    stalled_session_recoveries += 1
                    append_jsonl(progress_file, {
                        "event": "stalled_session_recovery",
                        "workspace": workspace_name,
                        "attempt": total_attempts,
                        "session_id": session_id,
                        "consecutive_unchanged_productive_attempts": (
                            consecutive_unchanged_productive_attempts
                        ),
                        "recovery": "force_fresh_session",
                    })
                    session_id = None
                    force_fresh_session = True
                    consecutive_unchanged_productive_attempts = 0

                last_failure_info = proof_info
                print(
                    f"  [{workspace_name}] attempt {total_attempts} preserved segmented proof_region skeleton, "
                    f"tokens={cumulative_tokens:,}, retry={retry_budget_retries_used()}/{max_retries}, continuing..."
                )
                time.sleep(2)
                continue

            if cleanup_info.get("shortcut_removed"):
                missing_segmented_skeleton = (
                    segmented_proof_workflow
                    and not proof_info.get("has_segmented_proof_region_skeleton")
                )
                if missing_segmented_skeleton:
                    proof_info["missing_segmented_skeleton"] = True
                    missing_skeleton_recoveries += 1
                    (
                        missing_skeleton_session_id,
                        missing_skeleton_session_streak,
                        use_fresh_session,
                    ) = _same_session_retry_or_fresh(
                        session_id,
                        missing_skeleton_session_id,
                        missing_skeleton_session_streak,
                    )
                    append_jsonl(progress_file, {
                        "event": "missing_segmented_skeleton_recovery",
                        "workspace": workspace_name,
                        "attempt": total_attempts,
                        "session_id": session_id,
                        "missing_skeleton_session_streak": missing_skeleton_session_streak,
                        "recovery": (
                            "force_fresh_session" if use_fresh_session else "retry_same_session"
                        ),
                    })
                    if use_fresh_session:
                        session_id = None
                        force_fresh_session = True
                    else:
                        force_fresh_session = False

                append_jsonl(progress_file, {
                    "event": "shortcut_removed",
                    "workspace": workspace_name,
                    "attempt": total_attempts,
                    "removed_shortcuts": cleanup_info.get("shortcut_cleanup_kinds", []),
                })

                if retry_budget_model_attempts() >= max_retries + 1:
                    summary["status"] = "retry_limit"
                    if exit_code is not None:
                        summary["exit_code"] = exit_code
                    summary.update(proof_info)
                    break

                last_failure_info = proof_info
                print(
                    f"  [{workspace_name}] attempt {total_attempts} removed forbidden shortcut "
                    f"({', '.join(cleanup_info.get('shortcut_cleanup_kinds', []))}), "
                    f"tokens={cumulative_tokens:,}, retry={retry_budget_retries_used()}/{max_retries}, continuing..."
                )
                time.sleep(2)
                continue

        if retry_budget_model_attempts() >= max_retries + 1:
            summary["status"] = "retry_limit"
            if exit_code is not None:
                summary["exit_code"] = exit_code
            summary.update(proof_info)
            break

        last_failure_info = proof_info
        print(
            f"  [{workspace_name}] attempt {total_attempts} done, "
            f"tokens={cumulative_tokens:,}, proof_ok={success}, "
            f"retry={retry_budget_retries_used()}/{max_retries}, continuing..."
        )
        time.sleep(2)

    elapsed = time.time() - t0
    summary["elapsed_seconds"] = round(prior_elapsed_seconds + elapsed, 1)
    if resume_state:
        summary["resume_elapsed_seconds"] = round(elapsed, 1)
    summary["finished_at"] = now_iso()
    summary["attempts"] = total_attempts
    summary["model_attempts"] = (
        prior_model_attempts + productive_attempts + noop_retry_charges
    )
    summary["noop_recoveries"] = prior_noop_recoveries + noop_recoveries
    summary["noop_retry_charges"] = noop_retry_charges
    summary["reasoning_output_exhaustion_recoveries"] = (
        reasoning_output_exhaustion_recoveries
    )
    summary["model_response_timeout_recoveries"] = model_response_timeout_recoveries
    summary["stalled_session_recoveries"] = stalled_session_recoveries
    summary["missing_skeleton_recoveries"] = missing_skeleton_recoveries
    if resume_state:
        summary["resume_attempts"] = attempt
        summary["resume_model_attempts"] = productive_attempts + noop_retry_charges
        summary["resume_noop_recoveries"] = noop_recoveries
    summary["max_retries"] = max_retries
    new_retries_used = max(
        0,
        productive_attempts
        + noop_retry_charges
        - (1 if reset_retries_on_resume else (0 if resume_state else 1)),
    )
    summary["retries_used"] = prior_retries_used + new_retries_used
    summary["retry_budget_model_attempts"] = retry_budget_model_attempts()
    summary["retry_budget_retries_used"] = retry_budget_retries_used()
    summary["retry_budget_max_retries"] = max_retries
    if resume_state:
        summary["resume_retries_used"] = new_retries_used
    summary["total_tokens"] = cumulative_tokens
    if resume_state:
        summary["resume_tokens"] = max(0, cumulative_tokens - prior_total_tokens)
    if session_id:
        summary["session_id"] = session_id
    if env.get("XDG_DATA_HOME"):
        summary["xdg_data_home"] = env["XDG_DATA_HOME"]

    if summary.get("status") not in ("success",):
        _, proof_info = check_proof_success(source_theorem_file, workspace_dir, theorem_file)
        if proof_info.get("proof_verified"):
            summary["status"] = "success"
        elif summary.get("status") not in ("timeout", "error", "token_limit", "retry_limit", "spec_violation"):
            summary["status"] = "incomplete"
        summary.update(proof_info)

    if spec_violation_detected:
        summary["status"] = "spec_violation"
        summary["spec_violation_detected"] = True
        if spec_violation_info:
            summary.update(spec_violation_info)

    summary["workspace_runtime_cleanup"] = cleanup_workspace_runtime_artifacts(workspace_dir)

    write_json(run_dir / "result.json", summary)
    append_jsonl(progress_file, {"event": "finish", **summary})
    return summary


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------


def parse_args(argv: list[str]) -> tuple[list[str], dict]:
    requested: list[str] = []
    with_paper = config_bool("OPENCODE_WITH_PAPER", False)
    options: dict = {
        "model": os.environ.get("OPENCODE_MODEL"),
        "model_variant": os.environ.get("OPENCODE_VARIANT"),
        "cases_dir": os.environ.get("OPENCODE_CASESTUDY_DIR"),
        "run_timeout_seconds": 12 * 3600,
        "model_response_timeout_seconds": MODEL_RESPONSE_TIMEOUT_SECONDS,
        "max_total_tokens": MAX_TOTAL_TOKENS,
        "max_retries": MAX_AGENT_RETRIES,
        "opencode_bin": os.environ.get("OPENCODE_BIN", str(DEFAULT_OPENCODE_BIN)),
        "stage_full_casestudy_workspace": with_paper,
        "full_prosa": config_bool("OPENCODE_FULL_PROSA", False),
        "full_prosa_source_dir": Path(
            os.environ.get("OPENCODE_FULL_PROSA_SOURCE_DIR", str(FULL_PROSA_SOURCE_ROOT))
        ),
        "segmented_proof_workflow": with_paper,
        "enable_skill": config_bool("OPENCODE_ENABLE_SKILL", False),
        "trace_requests": config_bool("OPENCODE_TRACE_REQUESTS", False),
        "skill_source_dir": DEFAULT_SKILL_SOURCE_DIR,
        "resume_run_dir": None,
        "output_dir": None,
        "fresh_session_on_resume": False,
        "reset_retries_on_resume": False,
        "preserve_retry_budget_on_resume": False,
        "_explicit_numeric_options": set(),
    }
    i = 0
    while i < len(argv):
        arg = argv[i]
        if arg == "--model":
            options["model"] = argv[i + 1]
            i += 2
        elif arg == "--variant":
            options["model_variant"] = argv[i + 1]
            i += 2
        elif arg == "--cases-dir":
            options["cases_dir"] = argv[i + 1]
            i += 2
        elif arg == "--run-timeout-seconds":
            options["run_timeout_seconds"] = int(argv[i + 1])
            options["_explicit_numeric_options"].add("run_timeout_seconds")
            i += 2
        elif arg == "--model-response-timeout-seconds":
            options["model_response_timeout_seconds"] = int(argv[i + 1])
            options["_explicit_numeric_options"].add("model_response_timeout_seconds")
            i += 2
        elif arg == "--max-total-tokens":
            options["max_total_tokens"] = int(argv[i + 1])
            options["_explicit_numeric_options"].add("max_total_tokens")
            i += 2
        elif arg == "--max-retries":
            options["max_retries"] = int(argv[i + 1])
            options["_explicit_numeric_options"].add("max_retries")
            i += 2
        elif arg == "--opencode-bin":
            options["opencode_bin"] = argv[i + 1]
            i += 2
        elif arg == "--stage-full-casestudy-workspace":
            options["stage_full_casestudy_workspace"] = True
            i += 1
        elif arg == "--full-prosa":
            options["full_prosa"] = True
            i += 1
        elif arg == "--full-prosa-source-dir":
            options["full_prosa_source_dir"] = Path(argv[i + 1])
            i += 2
        elif arg == "--segmented-proof-workflow":
            options["segmented_proof_workflow"] = True
            i += 1
        elif arg == "--skill":
            options["enable_skill"] = True
            i += 1
        elif arg == "--trace-requests":
            options["trace_requests"] = True
            i += 1
        elif arg == "--no-trace-requests":
            options["trace_requests"] = False
            i += 1
        elif arg == "--resume-run-dir":
            options["resume_run_dir"] = Path(argv[i + 1])
            i += 2
        elif arg == "--output-dir":
            options["output_dir"] = Path(argv[i + 1])
            i += 2
        elif arg == "--fresh-session-on-resume":
            options["fresh_session_on_resume"] = True
            i += 1
        elif arg == "--reset-retries-on-resume":
            options["reset_retries_on_resume"] = True
            i += 1
        elif arg == "--preserve-retry-budget-on-resume":
            options["preserve_retry_budget_on_resume"] = True
            i += 1
        elif arg in ("-h", "--help"):
            print(
                "Usage: run_casestudy_opencode_minprosa.py [OPTIONS] [WORKSPACE_NAME ...]\n\n"
                "Options:\n"
                "  --model PROVIDER/MODEL     Model to use (e.g. copilot/claude-sonnet-4)\n"
                "  --variant VARIANT          Model variant/reasoning effort (e.g. xhigh)\n"
                f"  --cases-dir DIR            Casestudy root directory (default: {DEFAULT_CASESTUDY_ROOT})\n"
                "  --run-timeout-seconds N    Timeout per workspace (default: 43200)\n"
                f"  --model-response-timeout-seconds N\n"
                f"                            Retry a silent model request after N seconds (default: {MODEL_RESPONSE_TIMEOUT_SECONDS})\n"
                f"  --max-total-tokens N       Token budget per workspace (default: {MAX_TOTAL_TOKENS})\n"
                f"  --max-retries N            Max productive continuation retries after the initial run (default: {MAX_AGENT_RETRIES})\n"
                f"  --opencode-bin PATH        Path to opencode binary/wrapper (default: {DEFAULT_OPENCODE_BIN})\n"
                "  --resume-run-dir DIR       Resume from an existing results/<run_dir> without restaging the workspace.\n"
                "  --output-dir DIR           Write a new run into an AutoAgent-reserved exact directory.\n"
                "  --fresh-session-on-resume  Resume with a continuation prompt but start a new session instead of reusing the old one.\n"
                "  --reset-retries-on-resume  Preserve lifetime counters but start a fresh initial-attempt-plus-retries budget epoch.\n"
                "  --preserve-retry-budget-on-resume\n"
                "                            Resume from the latest progress.jsonl counters and keep the active retry epoch.\n"
                "  --stage-full-casestudy-workspace\n"
                "                            Copy the entire source casestudy directory into the runtime workspace.\n"
                "  --full-prosa\n"
                "                            Copy the full Prosa source tree into runtime workspace/prosa.\n"
                f"  --full-prosa-source-dir DIR\n"
                f"                            Full Prosa source tree (default: {FULL_PROSA_SOURCE_ROOT})\n"
                "  --segmented-proof-workflow\n"
                "                            Enable the prooftex-first segmented workflow.\n"
                f"  --skill                    Import workspace-local skills from {DEFAULT_SKILL_SOURCE_DIR}\n"
                "  --trace-requests           Save full opencode request traces and copy them into each result directory.\n"
                "  --no-trace-requests        Disable request tracing even if OPENCODE_TRACE_REQUESTS=1.\n"
                "\nPositional: casestudy workspace names (directory names under the selected cases dir);\n"
                "  if omitted, all casestudy workspaces are run.\n"
            )
            raise SystemExit(0)
        else:
            requested.append(arg)
            i += 1
    return requested, options


def main() -> int:
    requested, options = parse_args(sys.argv[1:])
    resume_run_dir = options.get("resume_run_dir")
    output_dir = options.get("output_dir")
    existing_summaries: list[dict] = []
    existing_summary_by_workspace: dict[str, dict] = {}
    resume_config: dict = {}

    if resume_run_dir is not None and output_dir is not None:
        print("ERROR: --output-dir cannot be combined with --resume-run-dir", file=sys.stderr)
        return 1

    if options.get("reset_retries_on_resume") and options.get("preserve_retry_budget_on_resume"):
        print(
            "ERROR: --reset-retries-on-resume cannot be combined with --preserve-retry-budget-on-resume",
            file=sys.stderr,
        )
        return 1

    if resume_run_dir is not None:
        resume_run_dir = Path(resume_run_dir).expanduser().resolve()
        if not resume_run_dir.is_dir():
            print(f"ERROR: resume run dir not found: {resume_run_dir}", file=sys.stderr)
            return 1

        resume_config_payload = _read_json_payload(resume_run_dir / "config.json")
        if not isinstance(resume_config_payload, dict):
            print(f"ERROR: missing or invalid config.json in resume run dir: {resume_run_dir}", file=sys.stderr)
            return 1

        resume_config = resume_config_payload
        _apply_resume_config_defaults(options, resume_config)
        existing_summaries = _read_json_list(resume_run_dir / "summary.json")
        existing_summary_by_workspace = {
            entry["workspace"]: entry
            for entry in existing_summaries
            if isinstance(entry.get("workspace"), str)
        }

    cases_root = resolve_cases_root(options["cases_dir"])
    options["opencode_bin"] = str(Path(options["opencode_bin"]).expanduser().resolve())

    all_workspaces = sorted(casestudy_workspace_map(cases_root))
    if not all_workspaces:
        print(f"ERROR: no casestudy workspaces found under {cases_root}", file=sys.stderr)
        return 1

    if requested:
        workspaces = requested
    elif resume_run_dir is not None:
        resume_workspaces = resume_config.get("workspaces")
        if isinstance(resume_workspaces, list) and all(isinstance(item, str) for item in resume_workspaces):
            workspaces = resume_workspaces
        else:
            workspaces = all_workspaces
    else:
        workspaces = all_workspaces
    invalid = [w for w in workspaces if w not in all_workspaces]
    if invalid:
        print(f"ERROR: unknown workspace name(s): {', '.join(invalid)}", file=sys.stderr)
        print(f"Available: {', '.join(all_workspaces)}", file=sys.stderr)
        return 1

    if resume_run_dir is not None:
        base_run_dir = resume_run_dir
        progress_file = base_run_dir / "progress.jsonl"
    elif output_dir is not None:
        base_run_dir = consume_output_dir_reservation(Path(output_dir))
        progress_file = base_run_dir / "progress.jsonl"
        result_prefix, experiment_tag = resolve_result_prefix(options)
        write_json(
            base_run_dir / "config.json",
            {
                "runner": DEFAULT_RECORD_RUNNER,
                "result_prefix": result_prefix,
                "experiment_tag": experiment_tag,
                "stage_full_casestudy_workspace": options["stage_full_casestudy_workspace"],
                "prosa_mode": "full" if options["full_prosa"] else "minimal",
                "full_prosa": options["full_prosa"],
                "full_prosa_source_dir": str(options["full_prosa_source_dir"]),
                "segmented_proof_workflow": options["segmented_proof_workflow"],
                "skill_enabled": options["enable_skill"],
                "skill_source_dir": str(options["skill_source_dir"]),
                "trace_requests": options["trace_requests"],
                "model": options["model"],
                "model_variant": options["model_variant"],
                "cases_dir": str(cases_root),
                "run_timeout_seconds": options["run_timeout_seconds"],
                "model_response_timeout_seconds": options["model_response_timeout_seconds"],
                "max_total_tokens": options["max_total_tokens"],
                "max_retries": options["max_retries"],
                "opencode_bin": options["opencode_bin"],
                "workspaces": workspaces,
                "started_at": now_iso(),
                "output_dir_mode": "exact_reserved",
            },
        )
    else:
        result_prefix, experiment_tag = resolve_result_prefix(options)
        stamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        base_run_dir = RESULTS_ROOT / f"{result_prefix}_{stamp}"
        base_run_dir.mkdir(parents=True, exist_ok=True)
        progress_file = base_run_dir / "progress.jsonl"

        write_json(
            base_run_dir / "config.json",
            {
                "runner": DEFAULT_RECORD_RUNNER,
                "result_prefix": result_prefix,
                "experiment_tag": experiment_tag,
                "stage_full_casestudy_workspace": options["stage_full_casestudy_workspace"],
                "prosa_mode": "full" if options["full_prosa"] else "minimal",
                "full_prosa": options["full_prosa"],
                "full_prosa_source_dir": str(options["full_prosa_source_dir"]),
                "segmented_proof_workflow": options["segmented_proof_workflow"],
                "skill_enabled": options["enable_skill"],
                "skill_source_dir": str(options["skill_source_dir"]),
                "trace_requests": options["trace_requests"],
                "model": options["model"],
                "model_variant": options["model_variant"],
                "cases_dir": str(cases_root),
                "run_timeout_seconds": options["run_timeout_seconds"],
                "model_response_timeout_seconds": options["model_response_timeout_seconds"],
                "max_total_tokens": options["max_total_tokens"],
                "max_retries": options["max_retries"],
                "opencode_bin": options["opencode_bin"],
                "workspaces": workspaces,
                "started_at": now_iso(),
            },
        )

    summaries: list[dict] = []
    for workspace_name in workspaces:
        print(f"[start] {workspace_name}")
        try:
            resume_state = None
            if resume_run_dir is not None:
                resume_state = _load_resume_workspace_state(
                    base_run_dir,
                    workspace_name,
                    existing_summary_by_workspace.get(workspace_name),
                )
                if resume_state is not None and options.get("fresh_session_on_resume"):
                    resume_state["session_available"] = False
                    resume_state["fresh_session_on_resume"] = True
                if resume_state is not None and options.get("reset_retries_on_resume"):
                    resume_state["reset_retries_on_resume"] = True
                if resume_state is not None and options.get("preserve_retry_budget_on_resume"):
                    resume_state["preserve_retry_budget_on_resume"] = True
            summary = run_workspace(
                base_run_dir,
                workspace_name,
                progress_file,
                model=options["model"],
                model_variant=options["model_variant"],
                run_timeout_seconds=options["run_timeout_seconds"],
                model_response_timeout_seconds=options["model_response_timeout_seconds"],
                max_total_tokens=options["max_total_tokens"],
                max_retries=options["max_retries"],
                opencode_bin=options["opencode_bin"],
                cases_root=cases_root,
                stage_full_casestudy_workspace=options["stage_full_casestudy_workspace"],
                full_prosa=options["full_prosa"],
                full_prosa_source_dir=options["full_prosa_source_dir"],
                segmented_proof_workflow=options["segmented_proof_workflow"],
                enable_skill=options["enable_skill"],
                skill_source_dir=options["skill_source_dir"],
                trace_requests=options["trace_requests"],
                resume_state=resume_state,
            )
            summaries.append(summary)
            status = summary.get("status", "unknown")
            elapsed = summary.get("elapsed_seconds", "?")
            print(f"[done]  {workspace_name}  status={status}  elapsed={elapsed}s")
        except Exception as exc:
            print(f"[fail]  {workspace_name}: {exc}", file=sys.stderr)
            summaries.append({"workspace": workspace_name, "status": "error", "error": str(exc)})

    write_json(
        base_run_dir / "summary.json",
        _merge_workspace_summaries(existing_summaries, summaries) if resume_run_dir is not None else summaries,
    )

    success = sum(1 for s in summaries if s.get("status") == "success")
    total = len(summaries)
    print(f"\n{'='*50}")
    print(f"Results: {success}/{total} succeeded")
    print(f"Output:  {base_run_dir}")
    return 0 if success == total else 1


if __name__ == "__main__":
    if maybe_nohup(ROOT, Path(__file__).resolve(), sys.argv[1:]):
        raise SystemExit(0)
    exit_code = 1
    try:
        exit_code = main()
    except KeyboardInterrupt:
        finish_nohup_state(130, status="interrupted")
        raise SystemExit(130)
    except SystemExit as exc:
        child_exit_code = exc.code if isinstance(exc.code, int) else 1
        finish_nohup_state(child_exit_code)
        raise
    except Exception:
        finish_nohup_state(1, status="error")
        raise
    else:
        finish_nohup_state(exit_code)
        raise SystemExit(exit_code)
