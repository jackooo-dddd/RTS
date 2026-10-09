#!/usr/bin/env python3

from __future__ import annotations

import os
import runpy
import sys
from collections.abc import Iterator
from contextlib import contextmanager
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def _find_support_root() -> Path:
    required_files = (
        Path("scripts") / "opencode_runner_config.py",
        Path("scripts") / "run_casestudy_opencode_minprosa.py",
        Path("scripts") / "opencode_our_local.sh",
        Path("scripts") / "opencode_our_prompt.md",
    )
    for candidate in (ROOT, *ROOT.parents):
        if all((candidate / path).is_file() for path in required_files):
            return candidate
    raise RuntimeError("Could not locate runner support files for run_casestudy_our_minprosa.py")


SUPPORT_ROOT = _find_support_root()


def _first_existing_file(*candidates: Path) -> Path:
    for candidate in candidates:
        if candidate.is_file():
            return candidate
    raise RuntimeError(f"Missing required file. Tried: {', '.join(str(path) for path in candidates)}")


def _first_existing_dir(*candidates: Path) -> Path:
    for candidate in candidates:
        if candidate.is_dir():
            return candidate
    raise RuntimeError(f"Missing required directory. Tried: {', '.join(str(path) for path in candidates)}")


def _ensure_env_path(name: str, path: Path) -> None:
    current = os.environ.get(name)
    if current and Path(current).expanduser().exists():
        return
    os.environ[name] = str(path)


for search_path in (SUPPORT_ROOT, SUPPORT_ROOT / "scripts"):
    path_str = str(search_path)
    if path_str not in sys.path:
        sys.path.insert(0, path_str)
for search_path in (ROOT, ROOT / "scripts"):
    path_str = str(search_path)
    if path_str not in sys.path:
        sys.path.insert(0, path_str)

_CONFIG_HELPER = runpy.run_path(
    str(
        _first_existing_file(
            ROOT / "scripts" / "opencode_runner_config.py",
            SUPPORT_ROOT / "scripts" / "opencode_runner_config.py",
        )
    )
)
load_runner_config = _CONFIG_HELPER["load_runner_config"]
maybe_nohup = _CONFIG_HELPER["maybe_nohup"]
finish_nohup_state = _CONFIG_HELPER["finish_nohup_state"]

load_runner_config(ROOT)

OUR_PROMPT = _first_existing_file(
    ROOT / "scripts" / "opencode_our_prompt.md",
    SUPPORT_ROOT / "scripts" / "opencode_our_prompt.md",
)


def _default_result_prefix() -> str:
    if os.environ.get("OPENCODE_FULL_PROSA", "").lower() in {"1", "true", "yes", "on"}:
        return "our_casestudy_fullprosa"
    return "our_casestudy_minprosa"

_ensure_env_path(
    "OPENCODE_BIN",
    _first_existing_file(
        ROOT / "scripts" / "opencode_our_local.sh",
        SUPPORT_ROOT / "scripts" / "opencode_our_local.sh",
    ),
)
os.environ.setdefault("OPENCODE_RESULT_PREFIX", _default_result_prefix())
os.environ.setdefault("OPENCODE_RECORD_RUNNER", "run_casestudy_our_minprosa.py")
_ensure_env_path(
    "OPENCODE_SKILL_SOURCE_DIR",
    _first_existing_dir(
        Path("/home/junyi/prosabuddy/.opencode/skill"),
        ROOT / "opencode" / ".opencode" / "skill",
        SUPPORT_ROOT / "opencode" / ".opencode" / "skill",
    ),
)
_ensure_env_path(
    "OPENCODE_CASESTUDY_DIR",
    _first_existing_dir(
        Path("/home/junyi/dataset/Case_Study"),
        ROOT / "datasets_v06" / "casestudy_v06",
        SUPPORT_ROOT / "datasets_v06" / "casestudy_v06",
    ),
)
_ensure_env_path(
    "OPENCODE_MIN_PROSA_SOURCE_DIR",
    _first_existing_dir(
        Path("/home/junyi/prosabuddy/prosaworkspace"),
        ROOT / "datasets_v06" / "prosa_v06_classic",
        SUPPORT_ROOT / "datasets_v06" / "prosa_v06_classic",
    ),
)
_ensure_env_path(
    "OPENCODE_FULL_PROSA_SOURCE_DIR",
    _first_existing_dir(
        Path("/home/junyi/prosabuddy/prosaworkspace"),
        ROOT / "prosa_v06",
        SUPPORT_ROOT / "prosa_v06",
    ),
)

import run_casestudy_opencode_minprosa as base

base.RESULTS_ROOT = Path(os.environ.get("OPENCODE_RESULTS_ROOT", str(ROOT / "results"))).expanduser().resolve()
base.DEFAULT_CASESTUDY_ROOT = Path(os.environ["OPENCODE_CASESTUDY_DIR"]).expanduser().resolve()
base.PROSA_SOURCE_ROOT = Path(os.environ["OPENCODE_MIN_PROSA_SOURCE_DIR"]).expanduser().resolve()
base.FULL_PROSA_SOURCE_ROOT = Path(os.environ["OPENCODE_FULL_PROSA_SOURCE_DIR"]).expanduser().resolve()
base.DEFAULT_OPENCODE_BIN = Path(os.environ["OPENCODE_BIN"]).expanduser().resolve()
base.DEFAULT_SKILL_SOURCE_DIR = Path(os.environ["OPENCODE_SKILL_SOURCE_DIR"]).expanduser().resolve()
base.ENV_RESULT_PREFIX = os.environ.get("OPENCODE_RESULT_PREFIX")

DIRECT_PROSA_PROBE_MODE = "direct_prosa_probe"
DIRECT_PROSA_PROBE_AGENT = "whole-lemma"
ORIGINAL_RUN_WORKSPACE = base.run_workspace
ORIGINAL_INVOKE_OPENCODE = base._invoke_opencode


@contextmanager
def _temporary_env(overrides: dict[str, str | None]) -> Iterator[None]:
    previous = {key: os.environ.get(key) for key in overrides}
    try:
        for key, value in overrides.items():
            if value is None:
                os.environ.pop(key, None)
            else:
                os.environ[key] = value
        yield
    finally:
        for key, value in previous.items():
            if value is None:
                os.environ.pop(key, None)
            else:
                os.environ[key] = value


def _truthy_env(name: str, *, default: bool = False) -> bool:
    value = os.environ.get(name)
    if value is None:
        return default
    return value.lower() in {"1", "true", "yes", "on"}


def _positive_int_env(name: str, default: int) -> int:
    raw = os.environ.get(name)
    if not raw:
        return default
    try:
        value = int(raw)
    except ValueError:
        return default
    return value if value > 0 else default


def _direct_probe_steps() -> int:
    return _positive_int_env("OPENCODE_OUR_DIRECT_PROSA_PROBE_STEPS", 50)


def _direct_probe_agent() -> str:
    return os.environ.get("OPENCODE_OUR_DIRECT_PROSA_AGENT", DIRECT_PROSA_PROBE_AGENT).strip() or DIRECT_PROSA_PROBE_AGENT


def _direct_probe_timeout_seconds(default_timeout: int) -> int:
    configured = _positive_int_env("OPENCODE_OUR_DIRECT_PROSA_PROBE_TIMEOUT_SECONDS", min(default_timeout, 1800))
    return min(default_timeout, configured)


def _direct_probe_attempt() -> bool:
    return os.environ.get("OPENCODE_OUR_ATTEMPT_MODE") == DIRECT_PROSA_PROBE_MODE


def _adaptive_direct_probe_enabled(segmented_proof_workflow: bool) -> bool:
    if not segmented_proof_workflow:
        return False
    if _skip_segmentation_first_attempt():
        return False
    return _truthy_env("OPENCODE_OUR_DIRECT_PROSA_PROBE", default=True)


def _proof_workflow_env(
    segmented_proof_workflow: bool,
    extra_env: dict[str, str] | None,
) -> dict[str, str] | None:
    """Keep the ProsaBuddy controller mode aligned with the runner workflow.

    The segmented runner contract must not depend on the adaptive direct-probe
    branch to activate the corresponding ProsaBuddy guards.  In particular,
    resumed runs and configurations with the direct probe disabled still need
    the structured proof workflow.  Preserve an explicit caller override.
    """
    env = dict(extra_env or {})
    if segmented_proof_workflow:
        env.setdefault("OPENCODE_PROOF_WORKFLOW_MODE", "prooftex_structured_workflow")
    return env or None


def _workspace_target_v_file(workspace_dir: Path) -> Path | None:
    candidates = sorted(
        path
        for path in workspace_dir.glob("*.v")
        if base.is_casestudy_theorem_file(path)
    )
    return candidates[0] if candidates else None


def _invoke_opencode_with_target_file(
    cmd: list[str],
    *,
    env: dict[str, str],
    workspace_dir: Path,
    log_file: Path,
    json_log: Path,
    timeout_seconds: int,
    model_response_timeout_seconds: int = base.MODEL_RESPONSE_TIMEOUT_SECONDS,
    max_total_tokens: int | None = None,
    baseline_tokens: int = 0,
) -> tuple[int | None, bool, int | None, bool, bool]:
    next_cmd = list(cmd)
    if len(next_cmd) >= 2 and next_cmd[1] == "run" and _direct_probe_attempt() and "--agent" not in next_cmd:
        insert_at = max(2, len(next_cmd) - 1)
        next_cmd = [*next_cmd[:insert_at], "--agent", _direct_probe_agent(), *next_cmd[insert_at:]]

    if len(next_cmd) >= 2 and next_cmd[1] == "run" and "--file" not in next_cmd:
        target = _workspace_target_v_file(workspace_dir)
        if target is not None:
            insert_at = max(2, len(next_cmd) - 1)
            prompt_arg = next_cmd[-1]
            next_cmd = [*next_cmd[:insert_at], "--file", target.name, "--", prompt_arg]

    return ORIGINAL_INVOKE_OPENCODE(
        next_cmd,
        env=env,
        workspace_dir=workspace_dir,
        log_file=log_file,
        json_log=json_log,
        timeout_seconds=timeout_seconds,
        model_response_timeout_seconds=model_response_timeout_seconds,
        max_total_tokens=max_total_tokens,
        baseline_tokens=baseline_tokens,
    )


def _initial_read_guidance(theorem_file: Path) -> str:
    return (
        f"Begin by reading `proof.tex` if it exists, then read `{theorem_file.name}`, "
        "then inspect any directly relevant files under the current workspace.\n"
    )


def _direct_probe_read_guidance(theorem_file: Path) -> str:
    return (
        f"Begin by reading `{theorem_file.name}`. Do not read `proof.tex` during this run. "
        "Search only the target file and directly relevant files under `prosa/` for existing lemmas or proof patterns.\n"
    )


def _bridge_scope_text() -> str:
    return "the directly relevant facts in the current workspace"


def _first_attempt_override_section(theorem_file: Path) -> str:
    return (
        "\n\n## First Attempt Phase Override\n\n"
        "For this first attempt only, the instructions in this section override any conflicting generic benchmark restriction above.\n\n"
        "- You MUST read `proof.tex` first if it exists in the current workspace.\n"
        "- This first attempt is a theorem-structure pass: your immediate goal is to translate `proof.tex` into a faithful multi-step proof skeleton inside the target theorem body before deep lemma search.\n"
        "- You are the main theorem-level agent for this pass. Work through the proof narrative and theorem body at extremely fine granularity, line by line when needed, and materialize every introduced variable, witness, notation, set, interval, equality, inequality, bridge claim, and case split as explicit Coq code before moving on.\n"
        "- Treat `first-level` as the finest paper-sentence / bridge-fact layer, not as a whole branch, paragraph, displayed-equation derivation, or multi-step case argument. If one sentence or bridge can be stated as its own meaningful `pose`, `set`, `have`, `assert`, or local obligation, split it out before moving on.\n"
        "- When a first-level sentence or bridge remains pending, write it as its own explicit Coq focus block `{ ... }` so the split is visible in the file. Do not put multiple numbered steps, equation rewrites, residual bounds, branch-combination steps, or final conversion bridges inside one lemma-owned block.\n"
        "- For every object or bridge sentence introduced by `proof.tex`, emit the corresponding local `pose`, `set`, `have`, or `assert` statement in the file before you leave the surrounding step unresolved. Do not hide those steps only in comments.\n"
        "- Do NOT use placeholder claims such as `have H : True`, dummy names, or comment-only summaries to stand in for the paper's intermediate facts. Each named local step must carry its intended Coq term or proposition.\n"
        "- If one paper paragraph contains multiple inferential sentences, split them into multiple local named steps; a first-level `{ ... }` block is too coarse if it swallows several bridge facts that could already be stated separately.\n"
        "- If one proof sentence introduces multiple objects or performs multiple transformations, split that sentence into multiple consecutive local Coq lines instead of compressing them into one coarse step. If you are about to write a comment like `Step 1`, `Step 2`, and `Step 3` inside one pending block, split those steps into separate theorem-level nodes first.\n"
        "- Wrap each first-level local pending obligation with `(* proof_region begin owner: lemma admit_id: <stable_id> theorem: <theorem_name> kind: <kind> target: <target_name> plan_node: <node_id> depends_on: <deps> source: <source> input: <inputs> output: <output> layer: <layer> expected: <method> normal_form: <coq_goal_shape> evidence: <prosa_or_mathcomp_evidence> *)` immediately before the exported local `have`/`assert`/`suff` statement, and `(* proof_region end admit_id: <stable_id> *)` immediately after that statement's complete `{ ... }` proof block.\n"
        "- The `normal_form` field is a locality gate, not a prose description. It must be the same Coq proposition shape as the exported target statement after harmless notation normalization; do not write vague labels such as `equality of nat sums`, `Prop disjunction`, or `sum equality`.\n"
        "- Each first-level `proof_region` must own exactly one local pending theorem-level gap, marked by one stable `admit.` or `by admit.` site with an adjacent `admit_id` comment. Do not place sibling first-level gaps in the same region.\n"
        "- Use nested `{ ... }` blocks only for true local recursion inside one already-owned gap; sibling theorem-level modules must stay in separate brace-delimited blocks in paper order.\n"
        "- Once the theorem file contains those first-level admit-owned `proof_region owner: lemma` regions, stop local proof search inside those regions. The proof workflow scheduler will mechanically enqueue ready regions in file order; do not manually dispatch sibling lemma-owned regions or batch them yourself. If the scheduler reports `needs_subgoal_remodel` or `missing or invalid target_shape_review`, revise the stale region contract or split it into smaller regions before retrying; do not keep redispatching the same unchanged `admit_id`.\n"
        "- You MUST write that theorem-level decomposition back to the file before stopping this attempt.\n"
        "- Your job in this pass is to finish the detailed admit-based theorem decomposition. After that skeleton is present in the file, child proofs belong to scheduler-owned lemma-agent work, not prover-local grinding.\n"
        "- In this first attempt only, temporary `admit.` placeholders and a temporary final `Admitted.` terminator are allowed inside the target theorem body solely to preserve the step structure taken from `proof.tex`.\n"
        "- Do NOT use `Abort`, `Axiom`, `Hypothesis`, `Parameter`, or `Variable`.\n"
        "- Preserve the theorem statement exactly and keep all temporary gaps local to the existing proof body of the target theorem.\n"
        "- After the full first-level skeleton is in the file, you may discharge only trivial connector steps outside lemma-owned regions. Do not prove inside a `proof_region owner: lemma` region from the prover session; leave it for scheduler-owned lemma assignment.\n"
        "- Do not report a blocker until the multi-step admit skeleton is already written into the theorem body.\n\n"
        f"{_initial_read_guidance(theorem_file)}"
    )


def _skip_segmentation_first_attempt() -> bool:
    return os.environ.get("OPENCODE_SKIP_SEGMENTATION_FIRST_ATTEMPT", "").lower() in {
        "1",
        "true",
        "yes",
        "on",
    }


def _direct_proof_override_section(theorem_file: Path) -> str:
    return (
        "\n\n## Direct Proof Phase Override\n\n"
        "For this run, skip the theorem-structure / segmentation pass. The staged workspace may already contain a `proof.tex`-derived proof skeleton with `proof_block` and `admit_id` markers from a previous run.\n\n"
        "- Do NOT spend the first attempt decomposing `proof.tex` again or creating new segmentation-only admit blocks.\n"
        "- Treat the existing skeleton as the starting point if `proof_block` or `admit_id` markers are present. Preserve its block boundaries and stable IDs unless changing one local block is necessary to close that block.\n"
        "- Begin by reading `proof.tex` if useful, then read the current theorem file and immediately start replacing existing `admit.` / `Admitted.` gaps with real proof scripts.\n"
        "- Work one unresolved `proof_region owner: lemma` region at a time, in file order. If the runtime provides a `lemma_assignment`, replace exactly that assigned region; otherwise preserve the skeleton and let the scheduler enqueue the next region.\n"
        "- Temporary existing admits may remain only as not-yet-discharged local gaps while this attempt is still in progress. Do not add fresh placeholder admits except when preserving an already existing skeleton boundary, and never treat an admit-bearing file as a successful final answer.\n"
        "- The objective of this run is direct proof completion: finish by replacing all admits, ending the theorem with `Qed.`, and making `coqc` succeed.\n\n"
        f"{_initial_read_guidance(theorem_file)}"
    )


def _direct_prosa_probe_prompt(
    theorem_file: Path,
    theorem_name: str,
    theorem_statement: str,
    *,
    enable_skill: bool = False,
) -> str:
    template = OUR_PROMPT.read_text(encoding="utf-8")
    skill_specific = ""
    if enable_skill:
        skill_specific = (
            "Workspace-local skill support is enabled. Use a skill only if it directly helps locate an existing Prosa lemma or proof pattern; do not let skill use expand into paper-structured decomposition.\n\n"
        )
    specific = (
        "\n\n## Direct Prosa Proof\n\n"
        "Prove the target theorem directly from existing Prosa facts and the local theorem context. "
        "Direct proof is the main theorem-level strategy for this run.\n\n"
        f"The target file is `{theorem_file.name}`.\n"
        f"The theorem to prove is `{theorem_name}`.\n\n"
        "Only edit the existing proof body of the target theorem. The exact theorem declaration and statement must remain unchanged:\n\n"
        f"```coq\n{theorem_statement}\n```\n\n"
        "Do not read `proof.tex`, do not create a theorem-level paper skeleton, and do not introduce `proof_block`, `admit_id`, `admit`, or `Admitted`. "
        "Do not add helper definitions, local sections, contexts, variables, hypotheses, parameters, lemmas, or other top-level declarations.\n\n"
        "Search plan:\n"
        "1. Read the target theorem and nearby proof context in the target file.\n"
        "2. Search the theorem conclusion's key symbol names, hypothesis names, and relevant definition heads in `prosa/`.\n"
        "3. Inspect only directly relevant existing lemmas or proof patterns.\n"
        "4. Build the strongest direct proof you can justify from those existing facts, with only small local proof adaptations when necessary.\n"
        f"5. Validate with `coqc {theorem_file.name}`.\n\n"
        "Stay in direct theorem proof mode. Prefer existing Prosa lemmas and small local proof adaptations over paper-structured decomposition.\n\n"
        f"{_direct_probe_read_guidance(theorem_file)}"
        f"{skill_specific}"
        "Success requires `coqc` to succeed on the target file and the theorem to end with `Qed.`. If compilation fails, continue repairing the direct proof using only the target file and directly relevant files under `prosa/`."
    )
    return template + specific


def build_prompt(
    theorem_file: Path,
    theorem_name: str,
    theorem_statement: str,
    *,
    enable_skill: bool = False,
    segmented_proof_workflow: bool = False,
) -> str:
    if _direct_probe_attempt():
        return _direct_prosa_probe_prompt(
            theorem_file,
            theorem_name,
            theorem_statement,
            enable_skill=enable_skill,
        )

    template = OUR_PROMPT.read_text(encoding="utf-8")
    skip_segmentation = segmented_proof_workflow and _skip_segmentation_first_attempt()
    first_attempt_override = (
        _direct_proof_override_section(theorem_file)
        if skip_segmentation
        else _first_attempt_override_section(theorem_file)
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
        "This run is configured to skip the segmentation pass. The first attempt should immediately work on proving existing skeleton gaps or direct theorem steps. "
        "The run is finished only when `coqc` succeeds on the target file and the theorem ends with `Qed.`. If compilation fails, continue fixing the file instead of exiting."
        if skip_segmentation
        else
        "This first attempt is complete only after the multi-step proof skeleton from `proof.tex` is written into the theorem body with machine-readable `proof_region owner: lemma` regions and stable `admit_id`s, so the scheduler can enqueue unresolved lemma-owned regions, or there are no lemma-owned regions left. "
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
        "Only report a remaining blocker after at least one concrete bridge edit or proof-step attempt has been written and validated.\n\n"
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
        f"Once the theorem-level skeleton exists in the file, validate that the skeleton parses with:\n\n"
        f"```\ncoqc {theorem_file.name}\n```\n\n"
        "Then do not continue local proof search inside the prover session. Leave unresolved `proof_region owner: lemma` regions intact for scheduler-owned lemma delegation in file order; the scheduler will provide the `lemma_assignment` contract when a lemma agent is supposed to replace exactly one region.\n\n"
        f"{shortcut_policy}"
        "Do not stop, claim success, or exit early just because you wrote a proof script. "
        f"{completion_policy}"
    )
    return template + specific


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
    if _direct_probe_attempt():
        return _direct_prosa_probe_prompt(
            theorem_file,
            theorem_name,
            theorem_statement,
            enable_skill=enable_skill,
        )

    compile_error = base._trim_compile_error((proof_info or {}).get("compile_error"))
    skip_segmentation = segmented_proof_workflow and _skip_segmentation_first_attempt()
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
        if skip_segmentation:
            skeleton_section = (
                "This run is configured to skip the theorem-structure / segmentation pass. The current theorem body may contain a preexisting admit-based skeleton derived from `proof.tex`. "
                "Preserve that decomposition, keep existing gaps stable, and continue discharging those gaps one block at a time instead of restarting decomposition. "
                "If the runtime provides a `lemma_assignment`, discharge exactly that assigned `proof_region owner: lemma` region; otherwise preserve the skeleton and let the scheduler enqueue the next region. Do not batch sibling regions or replace the existing structure with a new segmentation. "
                "Temporary admits are no longer an acceptable final state for this retry; replace them with real proof scripts and finish with `Qed.`.\n\n"
            )
        else:
            skeleton_section = (
                "The first attempt was the theorem-structure pass. The current theorem body may already contain a multi-step admit-based skeleton derived from `proof.tex`. "
                "Preserve that decomposition, keep the existing first-level gaps stable, keep each first-level module inside its existing brace-delimited `{ ... }` block, rewrite any stale first-level `proof_block` header into the current `proof_region owner: lemma` form while preserving `admit_id` and block boundaries, and now discharge those gaps one region at a time instead of restarting from a blank proof. "
                "At the start of a fresh or recovered model session, if `proof.tex` has not yet been read in that live session, you MUST first use the read tool on `proof.tex` and then on the current theorem file before calling `task` or attempting any lemma dispatch. This is a session-state synchronization step; do not recreate or broaden the existing decomposition. "
                "If the runtime provides a `lemma_assignment`, discharge exactly that assigned `proof_region owner: lemma` region; otherwise preserve the skeleton and let the scheduler enqueue the next region. Do not batch sibling regions or keep proving inside lemma-owned regions from the prover session. "
                "Once that paper anchor is registered in the live session, do not reread it repeatedly. Temporary admits are no longer an acceptable final state for this retry.\n\n"
            )

    skill_specific = ""
    if enable_skill:
        skill_specific = (
            "Exception to the generic hard read scope above: workspace-local skill support remains enabled for this run. You may continue using skills discovered under `.opencode/skill/`, "
            "and those workspace-local skill files are permitted context. Do not read any other `.opencode` content unless it is part of using those workspace-local skills.\n\n"
        )
    bridge_specific = (
        f"Your previous stop does not count as completion. If you hit a missing-bridge blocker, resume by mining {_bridge_scope_text()}, "
        "instantiate candidate lemmas, and write the smallest local bridge skeleton that can be validated before stopping again.\n\n"
    )
    history_section = f"{history_compaction}\n\n" if history_compaction else ""

    return (
        f"The previous conversation ended but the proof is NOT yet complete.\n\n"
        f"The target file is `{theorem_file.name}`, the theorem is `{theorem_name}`.\n\n"
        "Only edit the existing proof body of the target theorem. The exact theorem declaration and statement must remain unchanged:\n\n"
        f"```coq\n{theorem_statement}\n```\n\n"
        f"This is retry {retry_index} of {max_retries}. Do not exit until `coqc {theorem_file.name}` succeeds.\n\n"
        f"{history_section}{skeleton_section}{shortcut_section}{compile_error_section}{skill_specific}{bridge_specific}"
        f"Please continue working. Read the current state of `{theorem_file.name}`, "
        f"fix the remaining proof or compilation issues, and keep iterating until `coqc {theorem_file.name}` "
        f"compiles successfully with the proof ending in `Qed.`.\n\n"
        "Do not cheat, do not weaken the theorem, do not add assumptions or placeholders, "
        "do not add top-level declarations or rewrite the surrounding file structure beyond an additive import line that is strictly required before the target theorem, "
        "and do not inspect or modify anything outside the staged workspace."
    )


def run_workspace(
    base_run_dir: Path,
    workspace_name: str,
    progress_file: Path,
    *,
    model: str | None = None,
    model_variant: str | None = None,
    run_timeout_seconds: int = 12 * 3600,
    model_response_timeout_seconds: int = base.MODEL_RESPONSE_TIMEOUT_SECONDS,
    max_total_tokens: int = base.MAX_TOTAL_TOKENS,
    max_retries: int = base.MAX_AGENT_RETRIES,
    opencode_bin: str = str(base.DEFAULT_OPENCODE_BIN),
    cases_root: Path | None = None,
    stage_full_casestudy_workspace: bool = False,
    full_prosa: bool = False,
    full_prosa_source_dir: Path = base.FULL_PROSA_SOURCE_ROOT,
    segmented_proof_workflow: bool = False,
    enable_skill: bool = False,
    skill_source_dir: Path = base.DEFAULT_SKILL_SOURCE_DIR,
    trace_requests: bool = False,
    extra_env: dict[str, str] | None = None,
    resume_state: dict | None = None,
) -> dict:
    workflow_env = _proof_workflow_env(segmented_proof_workflow, extra_env)
    if resume_state is not None:
        return ORIGINAL_RUN_WORKSPACE(
            base_run_dir,
            workspace_name,
            progress_file,
            model=model,
            model_variant=model_variant,
            run_timeout_seconds=run_timeout_seconds,
            model_response_timeout_seconds=model_response_timeout_seconds,
            max_total_tokens=max_total_tokens,
            max_retries=max_retries,
            opencode_bin=opencode_bin,
            cases_root=cases_root,
            stage_full_casestudy_workspace=stage_full_casestudy_workspace,
            full_prosa=full_prosa,
            full_prosa_source_dir=full_prosa_source_dir,
            segmented_proof_workflow=segmented_proof_workflow,
            enable_skill=enable_skill,
            skill_source_dir=skill_source_dir,
            trace_requests=trace_requests,
            extra_env=workflow_env,
            resume_state=resume_state,
        )

    if not _adaptive_direct_probe_enabled(segmented_proof_workflow):
        return ORIGINAL_RUN_WORKSPACE(
            base_run_dir,
            workspace_name,
            progress_file,
            model=model,
            model_variant=model_variant,
            run_timeout_seconds=run_timeout_seconds,
            model_response_timeout_seconds=model_response_timeout_seconds,
            max_total_tokens=max_total_tokens,
            max_retries=max_retries,
            opencode_bin=opencode_bin,
            cases_root=cases_root,
            stage_full_casestudy_workspace=stage_full_casestudy_workspace,
            full_prosa=full_prosa,
            full_prosa_source_dir=full_prosa_source_dir,
            segmented_proof_workflow=segmented_proof_workflow,
            enable_skill=enable_skill,
            skill_source_dir=skill_source_dir,
            trace_requests=trace_requests,
            extra_env=workflow_env,
            resume_state=resume_state,
        )

    probe_steps = _direct_probe_steps()
    probe_env = {
        **(extra_env or {}),
        "OPENCODE_PROOF_WORKFLOW_MODE": DIRECT_PROSA_PROBE_MODE,
        "OPENCODE_WHOLE_LEMMA_STEP_LIMIT": str(probe_steps),
        "OPENCODE_PROVER_STEP_LIMIT": str(probe_steps),
    }
    probe_agent = _direct_probe_agent()
    probe_base_run_dir = base_run_dir / "_direct_prosa_probe"
    probe_summary: dict | None = None

    base.append_jsonl(
        progress_file,
        {
            "event": "adaptive_direct_probe_start",
            "workspace": workspace_name,
            "step_limit": probe_steps,
            "agent": probe_agent,
        },
    )
    print(f"  [{workspace_name}] adaptive direct Prosa probe: agent={probe_agent} step_limit={probe_steps}")

    try:
        with _temporary_env({"OPENCODE_OUR_ATTEMPT_MODE": DIRECT_PROSA_PROBE_MODE}):
            probe_summary = ORIGINAL_RUN_WORKSPACE(
                probe_base_run_dir,
                workspace_name,
                progress_file,
                model=model,
                model_variant=model_variant,
                run_timeout_seconds=_direct_probe_timeout_seconds(run_timeout_seconds),
                model_response_timeout_seconds=model_response_timeout_seconds,
                max_total_tokens=max_total_tokens,
                max_retries=0,
                opencode_bin=opencode_bin,
                cases_root=cases_root,
                stage_full_casestudy_workspace=stage_full_casestudy_workspace,
                full_prosa=full_prosa,
                full_prosa_source_dir=full_prosa_source_dir,
                segmented_proof_workflow=False,
                enable_skill=enable_skill,
                skill_source_dir=skill_source_dir,
                trace_requests=trace_requests,
                extra_env=probe_env,
            )
    except Exception as exc:
        probe_summary = {"workspace": workspace_name, "status": "error", "error": str(exc)}

    if probe_summary.get("status") == "success":
        probe_summary["adaptive_workflow"] = "direct_prosa_probe"
        probe_summary["direct_probe_result_dir"] = str(probe_base_run_dir / workspace_name)
        probe_result_path = probe_base_run_dir / workspace_name / "result.json"
        if probe_result_path.parent.is_dir():
            base.write_json(probe_result_path, probe_summary)
        main_result_path = base_run_dir / workspace_name / "result.json"
        main_result_path.parent.mkdir(parents=True, exist_ok=True)
        base.write_json(main_result_path, probe_summary)
        base.append_jsonl(progress_file, {"event": "adaptive_direct_probe_success", **probe_summary})
        return probe_summary

    base.append_jsonl(
        progress_file,
        {
            "event": "adaptive_direct_probe_fallback",
            "workspace": workspace_name,
            "probe_status": probe_summary.get("status"),
            "probe_result_dir": str(probe_base_run_dir / workspace_name),
        },
    )
    print(
        f"  [{workspace_name}] direct probe status={probe_summary.get('status')}; "
        "restaging clean workspace for prooftex workflow"
    )

    fallback_env = {
        **(workflow_env or {}),
        "OPENCODE_PROOF_WORKFLOW_MODE": "prooftex_structured_workflow",
        "OPENCODE_PROVER_STEP_LIMIT": "",
    }

    with _temporary_env({"OPENCODE_OUR_ATTEMPT_MODE": None}):
        summary = ORIGINAL_RUN_WORKSPACE(
            base_run_dir,
            workspace_name,
            progress_file,
            model=model,
            model_variant=model_variant,
            run_timeout_seconds=run_timeout_seconds,
            model_response_timeout_seconds=model_response_timeout_seconds,
            max_total_tokens=max_total_tokens,
            max_retries=max_retries,
            opencode_bin=opencode_bin,
            cases_root=cases_root,
            stage_full_casestudy_workspace=stage_full_casestudy_workspace,
            full_prosa=full_prosa,
            full_prosa_source_dir=full_prosa_source_dir,
            segmented_proof_workflow=segmented_proof_workflow,
            enable_skill=enable_skill,
            skill_source_dir=skill_source_dir,
            trace_requests=trace_requests,
            extra_env=fallback_env,
        )
    summary["adaptive_workflow"] = "prooftex_structured_after_direct_probe"
    summary["direct_probe_status"] = probe_summary.get("status")
    summary["direct_probe_result_dir"] = str(probe_base_run_dir / workspace_name)
    result_path = base_run_dir / workspace_name / "result.json"
    if result_path.parent.is_dir():
        base.write_json(result_path, summary)
    return summary


def main() -> int:
    if not OUR_PROMPT.is_file():
        raise RuntimeError(f"Our prompt template not found: {OUR_PROMPT}")

    original_build_prompt = base.build_prompt
    original_build_continuation_prompt = base.build_continuation_prompt
    original_run_workspace = base.run_workspace
    original_invoke_opencode = base._invoke_opencode
    try:
        base.build_prompt = build_prompt
        base.build_continuation_prompt = build_continuation_prompt
        base.run_workspace = run_workspace
        base._invoke_opencode = _invoke_opencode_with_target_file
        return base.main()
    finally:
        base.build_prompt = original_build_prompt
        base.build_continuation_prompt = original_build_continuation_prompt
        base.run_workspace = original_run_workspace
        base._invoke_opencode = original_invoke_opencode


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
