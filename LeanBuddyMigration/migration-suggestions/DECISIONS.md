# Migration Decisions

All decisions taken for the ProsaBuddy → Lean 4 migration, in one place. Revision files under `gap-revisions/` and
the notes under `tools-advices/` follow these. Date: 2026-10-09.

## D1. Interactive backend — user decision

Pantograph replaces `coq_session` and `petanque`; Lean LSP gives file-level diagnostics; `lake build` performs
final verification. Details: [BACKEND_DECISION.md](BACKEND_DECISION.md).

## D2. Lean tool names — user decision

| Rocq tool | Lean tool | Backend | Notes |
|---|---|---|---|
| `coq_session` + `petanque` | **`lean_session`** | Pantograph | One interactive tool: open at a region, run tactic, read goals, keep/restore goal-state handles. |
| `coqtop` (Check/Print/About/Search) | **`lean_query`** | Pantograph environment/expression queries, or `#check`/`#print` in the target's context | Read-only; counts as a passive lookup. |
| `coqc` | **`lean_check`** | `lake env lean <file>` on the staged file | Per-step check; never the final verdict. |
| `checkpoint` | `checkpoint` (name kept) | `lean_check` + region analysis; final gate as D4 | |
| `proof_plan`, `task`, `read`, `edit`, `write`, `multiedit`, `apply_patch`, `grep`, `glob`, `skill`, `batch` | unchanged | | |
| `lsp` | `lsp` (name kept, reduced) | Lean language server | See D3. |
| `coq-check` (custom tool) | **`lean-check-file`** or merge into `lean_check` | | Decide when porting the custom tool; prefer merging. |

Rule: the model must never see a Rocq tool name in a prompt, permission list or reminder. All string lists in code
that name tools (guards, passive/active classification, cache sets, prune lists, permissions) use the new IDs.

## D3. Agent access to the Lean LSP tool — user decision

Enable the `lsp` tool for `prover` and `lemma` (and `explorer`) with **read-only lookup operations only**: hover,
go-to-definition, find-references, document symbols, workspace symbols. **No goal operation** (`proofGoals` is
removed from the Lean tool): goals the agent acts on come only from `lean_session`. Diagnostics are not a tool call;
they are attached automatically to edit/write results. The runner's workspace config must therefore allow `lsp`
(the Rocq runner denied it). All `lsp` calls count as passive lookups for the stall guards.

## D4. Proof-integrity audit — user decision

Replace the OCaml/astdump pipeline with a **semantic gate**, the approach of the Lean benchmark's
[`check.py`](../../Deliverables/lean-prosa-v06/benchmark/check.py):

1. frozen files unchanged (sha256 list: library, statement modules, `proof.tex`, configuration);
2. forbidden-token scan of the solution and every non-frozen helper module it imports (`sorry`, `admit`, `axiom`,
   `unsafe`, `implemented_by`, `@[extern`, `skipKernelTC`, `addDeclWithoutChecking`, `set_option debug.`,
   `run_cmd`, `run_elab`, `run_meta`, `#eval`, `initialize`, `elab`, `elab_rules`);
3. `lake build <solution module>`;
4. a fresh file `theorem benchmark_check : <statement> := <solution>` plus `#print axioms`, allowing only
   `propext`, `Classical.choice`, `Quot.sound`.

Per-region checks during the workflow use Lean syntax ranges of the `:= (by …)` region wrappers plus the same token
scan; they do not certify the theorem. No Lean AST-dump port of `classify_vernac_ast.ml` / `validate_classified_ast.py`.
The same function is the runner's success test and the agent's final theorem gate (KNOWN_PROBLEMS K9).

## D5. Retry accounting — user decision

Only real model attempts consume the proof-retry budget. **Free** (fresh session, no retry charged, reason recorded
in the progress log): controller/guard stops (`stalled_wide_fallback`, `materialization_livelock`,
`passive_lookup_stagnation`), transport/API errors (connection refused, HTTP 5xx, provider auth unavailable, model
response timeout), and attempts with zero tokens. A separate cap (e.g. 20 free recoveries per run) prevents endless
loops; hitting it ends the run with status `infrastructure_limit`, not `retry_limit`. This departs from the
original ProsaBuddy runner (KNOWN_PROBLEMS K3, S32); results are therefore not retry-for-retry comparable with the
Rocq replication.

## D6. Unused framework parts are not translated — user decision

Anything unused in the replication is dropped (GAPS.md §8): `.opencode/agent/`, `.opencode/command/`, custom tools
`coq-proof-dag`, `coq-serapi`, `pdf-read`, `github-pr-search`, `github-triage`, `.opencode/glossary/`,
`.opencode/themes/`, and (gap-revisions §5) the model-specific launch scripts in `scripts/scripts_junyi/`.

## D7. Routine decisions taken during the gap revisions (Claude, 2026-10-09)

| # | Decision | Where |
|---|---|---|
| R1 | Region wrapper and placeholders follow `prompt_revision.md` §0.1: delegated regions are `:= (by …)` blocks; the unfinished placeholder is `sorry`, allowed only inside approved regions during the scaffold phase. | gap-revisions §1, §2 |
| R2 | The prover still owns theorem closure, but Lean has no terminator: "closure" = the `solution` body has no `sorry` and passes D4. All `Admitted.` → `Qed.` instructions are removed. | gap-revisions §1 |
| R3 | The `proof.tex` gate (read first, then `proof_plan`, then skeleton) is kept unchanged; 22 of the 24 Lean case studies have `proof.tex`. | gap-revisions §1 |
| R4 | The agent identity becomes "LeanProver"; all Coq/SSReflect/MathComp guidance in system prompts is replaced by Lean/Mathlib guidance, Coq `Section` guidance by Lean `variable`/`section` guidance. | gap-revisions §2 |
| R5 | The runner targets the Lean benchmark layout: `Solution.lean` is the target, `Statement.lean` and `proof.tex` are read-only, success is D4. Reference solutions are never staged. | gap-revisions §5 |
| R6 | Tests: port the unit tests of translated modules to Lean fixtures; drop tests whose subject was removed (D6) or replaced (D4); tests that need a live Lean/Pantograph run become integration tests behind an environment flag. | gap-revisions §7 |
| R7 | The direct-probe mode (`direct_prosa_probe`, whole-lemma) is kept but not prioritised; it was unused in the replication. | gap-revisions §1 |

## D8. Known structural problems are fixed in the Lean version — user decision

The Lean version fixes KNOWN_PROBLEMS K2–K8 by design instead of porting the behaviour. Consequence: Lean results are
not directly comparable with the Rocq ProsaBuddy runs. Per-file changes: [known-problem-fixes/](known-problem-fixes/README.md).

## D9. Locked plan: bounded amendments (K2) — user decision

When a lemma helper escalates with `needs_preceding_bridge` (or `needs_subgoal_remodel` that names a missing preceding
fact), the prover may add a bridge node with its dependencies to the accepted plan through a dedicated
`proof_plan` amendment action. Up to **3 accepted amendments per plan**; a rejected amendment costs nothing; the
plan stays locked otherwise (no free re-planning). The amendment is reviewed like a plan node (contract fields,
dependencies, statement elaborates in context) and materialised as a new region before the escalated one.

## D10. Statements are compared by elaboration (K6, K7) — user decision

Root goals, plan-node statements (`normal_form`) and region targets are compared by elaborating both in the target
theorem's context (through `lean_session`, i.e. Pantograph) and testing definitional equality, not by text.
`kind` and `layer` are owned by the plan node and are not re-declared in the file (the region marker carries
no `kind`/`layer`; full field lists in the table below), so label drift cannot block a run. A formatting-only mismatch never spends a planning
revision. Plans whose `normal_form` is not a Lean proposition (prose) are rejected at plan time.

Field lists that follow from D10 (every prompt, parser and schema note uses these):

| Where | Fields |
|---|---|
| Region begin marker | `owner`, `admit_id`, `theorem`, `target`, `plan_node` |
| Contract comment in the file | `plan_node`, `depends_on`, `source`, `input`, `output`, `expected`, `normal_form`, `evidence` |
| `proof_plan` node only | `kind`, `layer` (plus the node's statement and dependencies) |

The parser still recognises `kind:`/`layer:` in a file comment (so the preceding value ends there), drops the value
with a warning, and never compares it with the plan.

The root goal of every benchmark task is a statement constant (`theorem solution : <thm>_statement.{u, v}`); how it
is opened, unfolded and compared is in
[known-problem-fixes/lean_session-equivalence.md](known-problem-fixes/lean_session-equivalence.md) §"Root goal".

## D11. Scheduling fixes (K4, K5, K8) — user decision

- **K5**: the decomposition plan and queue are keyed by (workspace, file, theorem); lemma-helper sessions and fresh
  main sessions read the same plan. A new session may change the plan only through D9 amendments.
- **K4**: when no region is dispatchable, the scheduler returns an explicit `no_ready_region` result with the reason
  and the required action (e.g. "region X escalated with needs_preceding_bridge: submit an amendment"), injected
  into the prover's next turn. The prover never waits for an assignment.
- **K8**: after **3 escalations of the same region with the same escalation type** and no source change that
  addresses them, the scheduler stops re-dispatching that region and requires a D9 amendment or a remodel.

## D12. Remaining known problems — routine decisions (Claude, 2026-10-09)

| Problem | Decision |
|---|---|
| K10 compaction | Every model in the Lean setup must declare `limit.context`; the runner refuses to start without it. Test compaction with real Lean goal states. |
| K11 workflow bypass (S14) | Allowed. A direct proof without regions is legitimate (2007-RTSS-Theorem1 found its proof that way); the final gate (D4) is what counts. The controller only requires a checkpoint before the prover reports success. |
| K11 solved state vs source (S26) | A region is "solved" only if the current staged source has no `sorry` in it and it elaborates; stored queue status is a cache that is recomputed from the source before every scheduling decision. |
| K11 stale diagnostics (S25) | Every diagnostic shown to the agent carries the source hash it belongs to; diagnostics for an older hash are dropped, not shown. |
| K11 API outage = idle model (S32) | Covered by D5. |
| K11 LSP tool vs prompts | Covered by D3; additionally remove every "`lsp proofGoals`" instruction from the prompts (`lemma.txt` L14, L84, L215; `whole-lemma.txt` L11; `proof-projection.ts` L238). |

## D13. Evidence prefixes (Claude, 2026-10-09)

The `evidence` field of a contract uses `prosa:`, `mathlib:`, `local:`, `context:`, `lean:`, `compiler:`
(`mathcomp:` → `mathlib:`, `coq:` → `lean:`; the other four unchanged). `prosa:`/`mathlib:` must name a declaration
that exists in the environment (checked with `lean_query`, i.e. Pantograph `env.inspect`); `lean:` is for core
Lean/`Init`/`Std` facts. The contract parser, the premise audit (`proof-workflow.ts`, candidate lists
`prosa_candidate_lemmas` / `mathlib_candidate_lemmas`, tools-advices `proof-plan-revision.md`) and the prompts
change together. A legacy prefix gives a review warning, not a block. Override this if you prefer other names; the
only requirement is one closed list shared by parser, audit and prompts.

## D14. Run staging and where the final check runs (Claude, 2026-10-09)

The build directory cannot be read-only, because `lake build <solution module>` (the agent's and `check.py` step 3)
and `check.py` step 4 (`.lake/benchmark/`) write into `.lake`. Each run copy therefore gets `.lake/packages`
linked read-only to the master build, a writable copy of the master `.lake/build`, and a writable
`.lake/benchmark`; the edit/write tools deny `.lake/**` and every frozen source. The runner's final check runs in a
fresh verification copy that receives only the agent's `CaseStudies/` files, never in the agent's workspace.
Layout: [TARGET_ENVIRONMENT.md, Run staging](../TARGET_ENVIRONMENT.md#run-staging-decisions-d14).

## Review fixes (2026-10-09)

A consistency review of these notes found the following; all are fixed in the linked files.

| Problem | Fix |
|---|---|
| Read-only `.lake` would make every final check fail | D14; TARGET_ENVIRONMENT *Run staging*; runner revision §3, §4, §6 |
| D10 not carried into the contract-field rules (K7 would come back) | D10 field lists; `proof-workflow-principles.txt-revision.md` L9/L13/L27; `proof-workflow-revision.md` §8; `prover.txt-fixes.md` (rules 8, 19a, 21, 22, §2); `proof-projection.ts-fixes.md` (18a); `proof-schema.ts-fixes.md`; `prompt_revision.md` §1.6 |
| D3 (no LSP goal operation) contradicted by "goal display" wording | BACKEND_DECISION table; `prompt_revision.md` §0.2; backend headers and recommendations of `lsp-`, `index-`, `server-`, `proof-context-revision.md`; tools-advices README |
| Root goal is a statement constant with universe parameters | `lean_session-equivalence.md` §"Root goal"; D10 note |
| Evidence prefixes undecided | D13; `prompt_revision.md` §1.3 |
| `native_decide` listed as a forbidden token in the runner note only | runner revision §5 (rejected by the axiom check, not a token) |
| Wrong toolchain link in BACKEND_DECISION rule 4 | now links `Deliverables/lean-prosa-v06/lean-toolchain`; Pantograph pinned |
| Leftover "decide whether…" wording | GAPS §1 and §5 rows, KNOWN_PROBLEMS K11 |
| Pantograph open questions | BACKEND_DECISION *Implementation answers* (checked against Pantograph 0.3.19 source) |

Second review (same day):

| Problem | Fix |
|---|---|
| `frontend.distil` takes text, not a path, and does not process `import` lines | BACKEND_DECISION: strip the header, REPL started with exactly those imports, restart on header or helper change; `lean_session-equivalence.md` item 5 |
| One error anywhere means no goals for any region | BACKEND_DECISION: distil a copy where every region that does not check is `sorry`; spike item 3 |
| `show b` accepts holes (`_`, `?x`) as equivalent to anything | `lean_session-equivalence.md` *No holes* (reject before the check; a leftover-metavariable check cannot catch it); `coq-session-revision.md` §6 |
| D10 prose said the marker carries only `plan_node`/`admit_id` | D10 prose now points to the field table (five marker fields) |
| 0.3.19 has no git tag; commit is on `dev` | BACKEND_DECISION and TARGET_ENVIRONMENT: check out the full commit |
| tools-advices README pointed compilation at `Prosa-Shunqi/` | links and wording now use `Deliverables/lean-prosa-v06/` (same files); GAPS references list too |
