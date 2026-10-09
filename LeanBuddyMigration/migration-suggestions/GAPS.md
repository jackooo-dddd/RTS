# Gaps: Rocq-Specific Parts of ProsaBuddy Not Yet Covered by the Migration Notes

The notes in `tools-advices/`, `skill-advices/` and `prompt-advices/` cover 42 TypeScript tool/workflow files, the
8 agent prompts (prover, lemma, fixer, diagnoser, explore, compaction, whole-lemma, title) and the 8 skills. The
items below also contain Rocq-specific behaviour. All are now decided: per-file changes are in [gap-revisions/](gap-revisions/README.md), decisions in [DECISIONS.md](DECISIONS.md).

Reference tree for every link: [`prosabuddy-rocq`](../prosabuddy-rocq/BASELINE.md)
(pure upstream commit `8e1de8c`, no replicate patches). `P` below abbreviates
`../prosabuddy-rocq/packages/opencode/src`.

Status of each gap: **open** = no note exists yet; **decided** = settled, see the linked decision.

## 1. Runtime controller: `session/prompt.ts` (3,364 lines) — decided, see [gap-revisions/01-prompt.ts-revision.md](gap-revisions/01-prompt.ts-revision.md)

The per-turn controller that injects runtime context, gates tools and stops turns. It is not covered by any note,
although much of the proof workflow's behaviour lives here.

| What | Where | Lean migration question |
|---|---|---|
| Accepted-plan hard tool gate (`read`, `grep`, `lsp`, `coqtop`, `proof_plan`, …) | [P/session/prompt.ts#L79](../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L79), [#L128](../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L128) | Rename to the Lean tool set (`lake env lean`, REPL/LSP goal tools). |
| Terminator ownership: `Admitted.` → `Qed.` only by the prover | [#L388-L390](../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L388) | Lean has no terminator; completion = no `sorry`, no errors, `#print axioms` clean. Define what "prover-owned closure" means. |
| `proof.tex` gate (must read, then `proof_plan`, then skeleton) | [#L589](../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L589), [#L1619-L1662](../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L1619) | Keep; rewrite "Coq proof file" / skeleton wording for Lean `:= by` blocks. |
| Phase-1 scaffold admits ("Temporary admits are permitted only inside …") | [#L1698](../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L1698) | `admit` → `sorry` inside regions; the scaffold is detected from Lean syntax ranges of the `:= (by …)` region wrappers (decided, D4 / R1). |
| Passive-lookup streaks and the `materialization_livelock` / `passive_lookup_stagnation` stop | [#L552](../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L552), [#L1502-L1561](../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L1502) | Which Lean tools count as "passive"; see KNOWN_PROBLEMS K3. |
| `stalled_wide_fallback` turn stop | [#L1210](../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L1210) | See KNOWN_PROBLEMS K3. |
| whole-lemma startup / lookup / proof-loop reminders | [#L1928-L1992](../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L1928) | Tool names and loop for Lean. |
| Proof-context injection for proof agents (live proof snapshot) | [#L205](../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L205), [#L2693](../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L2693) | Interactive goal state from Pantograph; LSP only for read-only display (BACKEND_DECISION.md). |

## 2. System prompts — decided, see [gap-revisions/02-system-prompts/](gap-revisions/02-system-prompts)

| File | Lines | Notes |
|---|---|---|
| [P/session/prompt/coqprover.txt](../prosabuddy-rocq/packages/opencode/src/session/prompt/coqprover.txt) | 146 | Base system prompt of every proof agent ("You are CoqProver"). Not in `prompt_revision.md`. |
| [P/session/prompt/proof-workflow-principles.txt](../prosabuddy-rocq/packages/opencode/src/session/prompt/proof-workflow-principles.txt) | 43 | Shared workflow principles appended to every proof agent. |
| [P/session/system.ts#L3-L25](../prosabuddy-rocq/packages/opencode/src/session/system.ts#L3) | 36 | Loads both prompts; the identity line `You are CoqProver powered by …`. |

## 3. Smaller source files with Rocq-specific code — decided, see [gap-revisions/03-small-source-files/](gap-revisions/03-small-source-files)

| File | Where | What changes |
|---|---|---|
| `agent/agent.ts` | [#L91-L95](../prosabuddy-rocq/packages/opencode/src/agent/agent.ts#L91), [#L140-L144](../prosabuddy-rocq/packages/opencode/src/agent/agent.ts#L140), [#L170](../prosabuddy-rocq/packages/opencode/src/agent/agent.ts#L170) | Per-agent permissions name `coqc`, `coqtop`, `coq_session`, `petanque`, `lsp`, `checkpoint`; must match the renamed Lean tools. |
| `session/compaction.ts` | [#L95](../prosabuddy-rocq/packages/opencode/src/session/compaction.ts#L95), [#L228-L263](../prosabuddy-rocq/packages/opencode/src/session/compaction.ts#L228), [#L390](../prosabuddy-rocq/packages/opencode/src/session/compaction.ts#L390) | Prune-protected tool list and the compaction template (`.v` files, rocq-lsp snapshot). |
| `cli/cmd/run.ts` | [#L24-L25](../prosabuddy-rocq/packages/opencode/src/cli/cmd/run.ts#L24), [#L75-L79](../prosabuddy-rocq/packages/opencode/src/cli/cmd/run.ts#L75), [#L154](../prosabuddy-rocq/packages/opencode/src/cli/cmd/run.ts#L154) | Benchmark-prompt detection (`Coq|Rocq`, `.v`, `coqc`), `coqc` output rendering. |
| `session/message-v2.ts` | [#L780-L781](../prosabuddy-rocq/packages/opencode/src/session/message-v2.ts#L780) | Cache tool sets name `coqtop`, `coqc`, `coq_session`, `checkpoint`, `proof_plan`. |
| TUI (`cli/cmd/tui/…`) | — | Cosmetic (brand, LSP status). Low priority. |

## 4. AST / declaration-integrity audit backend — decided (DECISIONS D4), see [gap-revisions/04-audit-backend/](gap-revisions/04-audit-backend/README.md)

`coq-ast-audit-revision.md` says "replace with Lean syntax and elaboration information" but gives no design. The
current backend is three programs outside TypeScript:

- [scripts/classify_vernac_ast.ml](../prosabuddy-rocq/scripts/classify_vernac_ast.ml) (262 lines, OCaml; classifies the coq-lsp `astdump` output),
- [scripts/validate_classified_ast.py](../prosabuddy-rocq/scripts/validate_classified_ast.py) (1,021 lines; the rules: statement unchanged, no `Admitted`/`admit`/`Axiom`, allowed vernaculars inside proofs, exterior unchanged),
- the elaboration-dump plugin (`scripts/prosabuddy_elaboration_dump_plugin/`, `extract_elaboration.py`).

Needed: a Lean design that specifies (a) how the target declaration's statement is compared (elaborated type,
`isDefEq` or syntactic), (b) the forbidden set (`sorry`, `admit`, `axiom`, `unsafe`, `set_option` escapes,
`@[implemented_by]`, `local instance` changes…), (c) `#print axioms` on the target, (d) what may change outside
the proof, including the **import policy** (see KNOWN_PROBLEMS K1).

## 5. Benchmark runner — decided, implement last (after the app translation), see [gap-revisions/05-benchmark-runner/](gap-revisions/05-benchmark-runner/README.md)

**What it is:** the Python harness that runs ProsaBuddy on one benchmark task: it stages a workspace (target file,
`proof.tex`, the Prosa library), starts `opencode run` with the task prompt, retries, and decides success. It is
code to port, not data: the case studies themselves are already translated. In Lean the runner operates on the
translated package [`Deliverables/lean-prosa-v06`](../../Deliverables/lean-prosa-v06/README.md): the 24 case studies
([benchmark/README.md](../../Deliverables/lean-prosa-v06/benchmark/README.md)) and the 130-theorem Prosa benchmark
([benchmark/prosa-theorems/README.md](../../Deliverables/lean-prosa-v06/benchmark/prosa-theorems/README.md)).

**The Lean benchmark already defines most of what the runner must do:**

- Target: `CaseStudies/<G>/<F>/Solution.lean` (`theorem solution : <thm>_statement := by sorry`); `Statement.lean`
  and `proof.tex` are read-only; helper modules may be added under `CaseStudies/`; the task list is
  `benchmark/tasks.json`. This replaces Rocq theorem-range extraction (`_extract_target_theorem_ranges`) and most of
  the statement-integrity check: the statement is a frozen `Prop` constant in a read-only module.
- Success: [`benchmark/check.py`](../../Deliverables/lean-prosa-v06/benchmark/check.py) (frozen-file sha256 check,
  forbidden-token scan of the solution and its helper modules, `lake build <solution module>`, then a fresh file
  `theorem benchmark_check : <statement> := <solution>` with `#print axioms`, allowing only `propext`,
  `Classical.choice`, `Quot.sound`). Use it as the runner's success test and as the agent's final gate
  (KNOWN_PROBLEMS K9).
- Staging: copy the package with a prebuilt `.lake` (`lake exe cache get` + `lake build`), **without the reference
  solutions** (distributed separately; they must never be visible to the agent).

Still to port from the Rocq runner:

[scripts/scripts_junyi/run_casestudy_opencode_minprosa.py](../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py) (4,281 lines) has no note. Rocq-specific parts:

| Function | Line | Lean equivalent to define |
|---|---|---|
| `target_theorem_kind/name`, `_extract_target_theorem_ranges` | [#L383](../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L383), [#L407](../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L407) | Locate `theorem`/`lemma` and its `:= by` body in `.lean`. |
| `inspect_theorem_edit_integrity` | [#L514](../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L514) | Statement/prefix/suffix integrity for Lean. |
| `workspace_coq_environment`, `stage_workspace`, `stage_proof_tex_alias` | [#L626](../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L626), [#L779-L801](../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L779) | Stage a Lake project with a prebuilt Mathlib/Prosa cache instead of `_CoqProject` + copied `.v`. |
| `write_opencode_config` (permissions, `bash: coqc *`, `lsp: deny`) | [#L888](../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L888) | `lake env lean <file>`; `lsp` allowed, read-only lookups only (decided, D3). |
| `build_prompt`, `build_continuation_prompt` | [#L987](../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L987), [#L1292](../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L1292) | All retry prompts ("Do not exit until `coqc …` succeeds", forbidden shortcuts). |
| `check_proof_success` | [#L1468](../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L1468) | Success = file compiles, no `sorry`, target has no `sorryAx`/new axioms. Must agree with the in-agent final gate (KNOWN_PROBLEMS K9). |
| `cleanup_forbidden_shortcuts` | [#L1632](../prosabuddy-rocq/scripts/scripts_junyi/run_casestudy_opencode_minprosa.py#L1632) | Remove `sorry`/`admit`/`axiom` instead of `Admitted`/`admit`/`Axiom`. |

## 6. Interactive Lean backend — decided (2026-10-09)

**Pantograph** is the interactive backend (replaces `coq_session` and `petanque`), **Lean LSP** gives file-level
diagnostics, and **`lake build`** does final verification. Details, responsibilities and the remaining
implementation questions: [BACKEND_DECISION.md](BACKEND_DECISION.md).

## 7. Tests — decided (DECISIONS R6), see [gap-revisions/07-tests/](gap-revisions/07-tests/README.md)

`packages/opencode/test/` (e.g. `test/session/proof-workflow.test.ts`, `test/tool/coq-session.test.ts`,
`test/session/prompt.test.ts`) uses Rocq fixtures and expectations. A Lean fixture set is needed before the
workflow can be refactored safely. Note: 9 tests in `prompt.test.ts` already time out (5 s) on pristine
`8e1de8c` in our environment; they are not a migration signal.

## 8. Unused framework files — removed, not translated (2026-10-09)

User decision: anything not used in the replication is not translated. Removed from the baseline tree and from the notes
(all recoverable from this repository's commit `d577db4b`, `prosabuddy/`):

| Removed | Evidence it was unused |
|---|---|
| `.opencode/agent/` (8 agents: casestudy-prover, coq-prover, docs, duplicate-pr, paper-analyst, proof-orchestrator, translator, triage) | Our trees never contained them; across 38 run databases the `task` tool dispatched only lemma, prover, explorer, diagnoser and fixer. |
| `.opencode/command/` (9 slash commands) | Interactive TUI commands; the benchmark runner drives `opencode run` and never invokes them. |
| Custom tools `coq-proof-dag`, `coq-serapi`, `pdf-read` and their notes | Offered to the model in every run, 0 calls in 38 runs. |
| Custom tools `github-pr-search`, `github-triage` and their notes | Not present in our trees, never offered; unrelated to proving. |
| `.opencode/glossary/` (17 files), `.opencode/themes/` | OpenCode interface translations and colour theme. |

Kept: custom tool `coq-check` (5 calls in 4 runs) and its note.

Follow-ups for the Lean code:

1. Core code still names `coq-prover` in two agent sets:
   [task.ts#L55](../prosabuddy-rocq/packages/opencode/src/tool/task.ts#L55) (`WIDE_PROBE_PROOF_AGENTS`) and
   [proof-workflow.ts#L525](../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L525) (`WIDE_PROOF_EDIT_AGENTS`). Drop these entries.
2. The accepted-plan tool gate lists the removed tools `coq-proof-dag` and `pdf-read`
   ([prompt.ts#L92-L93](../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L92)). Drop them.
3. Keep the Lean version's config directory free of agent/command files: the runner points `OPENCODE_CONFIG_DIR` at
   `.opencode/` ([opencode_runner_config.py#L73](../prosabuddy-rocq/scripts/scripts_junyi/opencode_runner_config.py#L73)),
   so any `subagent` definition placed there becomes available to the prover's `task` tool.

## 9. Data the runs need (exists; listed for completeness)

- Lean case studies and the 130-theorem benchmark: `../Deliverables/lean-prosa-v06/` (CaseStudies, benchmark).
- Lean Prosa environment: [`Deliverables/lean-prosa-v06/`](../../Deliverables/lean-prosa-v06/README.md) (lean-toolchain, lakefile, Mathlib pin; see [TARGET_ENVIRONMENT](../TARGET_ENVIRONMENT.md)). `Prosa-Shunqi/` is the development workspace it was exported from.
- Paper proofs: `proof.tex` per case study (`../RTS_Papers/*/proof.tex`, also in `Deliverables/lean-prosa-v06/CaseStudies/*/*/`).
