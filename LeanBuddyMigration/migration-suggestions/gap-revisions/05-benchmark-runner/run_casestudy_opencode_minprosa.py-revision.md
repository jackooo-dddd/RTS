# Revision: `scripts/scripts_junyi/run_casestudy_opencode_minprosa.py` (core runner)

**File**: [`run_casestudy_opencode_minprosa.py`](../../../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py) (4,281 lines). **Change size**: Modify, Large (staging, success, prompts, retry accounting).
**Follows**: DECISIONS D2, D3, D4, D5, R5.

**1. Task layout and target theorem | Rewrite, Medium**

- **Location**: `is_casestudy_theorem_file` / `casestudy_workspace_map` / `root_theorem_file` [#L330-L381](../../../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L330), `target_theorem_kind/name` [#L383-L406](../../../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L383), `_extract_target_theorem_ranges` [#L407](../../../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L407), `extract_target_theorem_statement` [#L457](../../../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L457).
- **Current**: case-study folders hold one `<Name>.v`; the target is the last `Theorem/Lemma` ending in `Admitted.`; its body range is found by Coq keywords.
- **Change** (R5): read `benchmark/tasks.json` (id, folder, statement module, solution module, statement name, hint file). Target file = `CaseStudies/<G>/<F>/Solution.lean`; theorem name = `solution`; statement text for the prompt = the `<thm>_statement` definition from `Statement.lean`. The body range is the `:= by …` of `solution` (Lean syntax ranges; prompt_revision §0.1 for region wrappers).

**2. Edit integrity | Simplify, Small**

- **Location**: `inspect_theorem_edit_integrity` [#L514](../../../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L514).
- **Change**: replace by "frozen files unchanged" (sha256, `benchmark/frozen_sha256.json`) + "`solution` still has type `<thm>_statement`" — both part of the D4 gate. Helper declarations and package `import`s in `Solution.lean` are allowed (KNOWN_PROBLEMS K1).

**3. Workspace staging | Rewrite, Medium**

- **Location**: `write_workspace_coq_project` [#L621](../../../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L621), `workspace_coq_environment` [#L626](../../../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L626), `_preflight_import_commands` [#L634](../../../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L634), `stage_proof_tex_alias` [#L779](../../../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L779), `stage_workspace` [#L801](../../../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L801), `stage_workspace_skill` [#L873](../../../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L873).
- **Current**: copies the case `.v`, `proof.tex` and the Prosa `.v`/`.vo` tree, writes `_CoqProject` (`-R prosa prosa`), sets `COQPATH`/`ROCQPATH`, preflights `Require` commands.
- **Change**: stage a copy of the Lean package (`lakefile.lean`, `lake-manifest.json`, `lean-toolchain`, `Prosa/`, `CaseStudies/` **without any reference solution**, `benchmark/check.py`, `frozen_sha256.json`, `tasks.json`) and set up `.lake` as in [TARGET_ENVIRONMENT, Run staging](../../../TARGET_ENVIRONMENT.md#run-staging-decisions-d14) (D14): `.lake/packages` linked read-only to the master build (built once with `lake exe cache get` + `lake build`), `.lake/build` a writable per-run copy of the master's, `.lake/benchmark` writable for `check.py`. Preflight = `lake env lean` on `Statement.lean`. Environment: `ELAN_HOME`/`PATH` to the pinned toolchain (v4.33.1); no COQ variables. Skills staging unchanged.

**4. Workspace configuration (permissions) | Modify, Small**

- **Location**: `write_opencode_config` [#L888](../../../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L888).
- **Current**: `"lsp": "deny"`, `question/webfetch/websearch: deny`, `bash: {"coqc <file>": allow, "coqc *": allow}`.
- **Change**: `"lsp": "allow"` (read-only operations only, enforced in the tool, D3); keep `question/webfetch/websearch: deny`; bash allow-list `lake env lean <file>` and `lake build <solution module>` instead of `coqc`; edit/write deny `.lake/**`, `Prosa/**`, `benchmark/**`, `**/Statement.lean`, `**/proof.tex` (D14).

**5. Prompts | Modify, Medium**

- **Location**: `_initial_read_guidance` [#L299](../../../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L299), `_first_attempt_override_section` [#L959](../../../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L959), `build_prompt` [#L987](../../../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L987), `build_continuation_prompt` [#L1292](../../../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L1292).
- **Change**: "`coqc X.v` succeeds and the theorem ends with `Qed.`" → "the final gate passes for `Solution.lean`" (D4); statement shown in a ```lean block; forbidden-shortcut list → the D4 token list (`sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `@[extern`, `skipKernelTC`, `addDeclWithoutChecking`, `set_option debug.`, `run_cmd`, `run_elab`, `run_meta`, `#eval`, `initialize`, `elab`, `elab_rules`). `native_decide` is not in the token list; the axiom check rejects it (it adds `Lean.ofReduceBool`), so the prompt names it separately as "rejected by the final gate". The wrapper's prompts override most of these (see `run_casestudy_our_minprosa.py-revision.md`).

**6. Success check | Replace, Medium**

- **Location**: `check_proof_success` [#L1468](../../../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L1468), `_preserve_first_attempt_admit_skeleton` / `_has_segmented_proof_region_skeleton` [#L1449-L1466](../../../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L1449).
- **Change** (D4, K9): success = `python3 benchmark/check.py <task-id> --json` returns PASS in a fresh verification copy that contains only the agent's `CaseStudies/` files (D14), never in the agent's workspace. Keep the "first-attempt skeleton retained" logic, with "admit skeleton" = `sorry` only inside proof regions.

**7. Shortcut cleanup | Modify, Small**

- **Location**: `_sanitize_forbidden_shortcuts_in_proof_body` [#L1561](../../../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L1561), `cleanup_forbidden_shortcuts` [#L1632](../../../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L1632).
- **Change**: remove/flag `sorry`/`admit` outside regions, `axiom` declarations and the D4 escape tokens, instead of `Admitted.`/`admit`/`Abort`/`Axiom`/`Hypothesis`/`Parameter`/`Variable`.

**8. Retry accounting | Modify, Medium (D5)**

- **Location**: limits [#L932-L941](../../../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L932); no-op ladder `_same_session_retry_or_fresh` [#L944](../../../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L944) and `_should_charge_noop_recovery` [#L1827](../../../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L1827); productive-attempt charge [#L3262-L3266](../../../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L3262); planning-exhaustion fresh session with `retry_consumed: True` [#L3395-L3445](../../../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L3395); model-timeout recovery [#L3448](../../../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L3448); no-op charging [#L3499-L3590](../../../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L3499).
- **Change**:
  - Never charge a proof retry for: a controller stop (recognised by the structured `controller_stop` record, gap-revisions §1 item 8), a transport/API error (connection refused, HTTP 5xx, provider "auth_unavailable"), a model-response timeout, or a zero-token attempt.
  - Count these in a separate `infrastructure_recoveries` counter with its own cap (default 20); hitting it ends the run with status `infrastructure_limit`.
  - The planning-budget exhaustion (L3407, L3439) becomes free as well when its cause is a format-only rejection (KNOWN_PROBLEMS K6).
  - Print the real budget in every attempt line (`retry=k/8 infra=m/20`); the Rocq runner printed only part of it.

**Retained unchanged**: result folders, `summary.json`/`progress.jsonl` formats (add the new fields), token/time limits, resume support, request tracing.
