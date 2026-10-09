# ProsaBuddy replication (Rocq, single theorem, gpt-6-luna)

Replicates ProsaBuddy case-study experiments one theorem at a time (`2005-ECRTS-Lemma3`, `2007-RTSS-Theorem2`, `2007-RTSS-Theorem3`)
with the original ProsaBuddy agents, prompts, skills, tools and experiment runner. The differences are the model
(`gpt-6-luna` through a local CLIProxyAPI), the Rocq/Prosa environment of this machine (opam switch `prosa-0.6`),
and ten runtime fixes (`patches/01-proof-loop-fixes.patch`, see below).

Source of everything copied: `../prosabuddy` (ProsaBuddy commit `af8f06d`, which carries the `f692cb7`
"AST-audited proof workflow safeguards" code).

## Layout

| Path | Contents | Copied from |
|---|---|---|
| `prosabuddy/` | The ProsaBuddy app (OpenCode fork; same layout as the original `prosabuddy/`): root manifests + `bun.lock`, `packages/{opencode,plugin,sdk,util,script}` (no `test/`, Dockerfile, dev docs) | `prosabuddy/` |
| `prosabuddy/.opencode/` | The 8 proof skills, custom Coq/PDF tools (`coq-check`, `coq-proof-dag`, `coq-serapi`, `pdf-read`), `opencode.jsonc` (no translation glossary/themes; the `.md` project agents, slash commands and GitHub tools were removed) | `prosabuddy/.opencode/` |
| `prosabuddy/scripts/` | AST validator used by the runtime AST audit (`coq-ast-audit.ts` resolves `<app>/scripts`) | `prosabuddy/scripts/` |
| `scripts/` | Experiment runner and its support files, in the layout the runner expects (`ROOT/scripts`) | `prosabuddy/scripts/scripts_junyi/` |
| `scripts/opencode_runner_config.env` | Original runner settings; only `/home/junyi` paths replaced, `PARALLEL=1` | rewritten |
| `scripts/run_case_gpt6luna.sh` | Launcher for this replication (mirrors the original launcher) | new |
| `prosa_v06/` | Prosa v0.6 (`analysis behavior implementation model results util`) + ProsaBuddy's `classic`, `.v` sources compiled here with Rocq 9.0.1 | `prosabuddy/prosaworkspace/` (symlinks resolved) |
| `datasets_v06/casestudy_v06/<case>/` | Case-study inputs (`.v` + paper PDF): `2005-ECRTS-Lemma3`, `2007-RTSS-Theorem2`, `2007-RTSS-Theorem3` | `../RTS_Papers/<case>/` |
| `patches/` | Every change made to ProsaBuddy source, as unified diffs against `../prosabuddy` | new |
| `results/` | Run outputs: staged workspace, logs, request traces, per-attempt records (git-ignored) | generated |
| `.tools/bin/bun` | Bun 1.3.10, the version ProsaBuddy pins (`packageManager`) | GitHub release |
| `gptAPITest/.env` | Local CLIProxyAPI URL + key read by the launcher (git-ignored; the smoke test that used to live here was removed) | earlier setup |

## Same as the original experiment

- Agents: the built-in ProsaBuddy agents `prover` (entry agent) → `lemma`, `fixer`, `diagnoser`, `explorer`,
  `whole-lemma`, with the unmodified `.txt` prompts in `prosabuddy/packages/opencode/src/agent/prompt/`. No `.md`
  agents: the project agents of `prosabuddy/.opencode/agent/` are not copied, and `opencode.jsonc` disables them by name.
- Skills: all 8 skills in `.opencode/skill/`, enabled with `--skill`.
- Runner: `run_casestudy_our_minprosa.py` with the original flags `--stage-full-casestudy-workspace --full-prosa
  --segmented-proof-workflow --skill --trace-requests`, 80M token budget, 8 retries, 12 h timeout,
  `OPENCODE_OUR_DIRECT_PROSA_PROBE=0`, strict workspace boundary, success = target ends in `Qed.`, no
  admits/axioms, no edits outside the proof, and an independent `coqc` passes.

## Differences (and why)

| Item | Original | Here | Reason |
|---|---|---|---|
| Model | `codexproxy/gpt-5.4` (xhigh) for this theorem; `gpt-5.6-luna` (max) in other runs | `codexproxy/gpt-6-luna`, variant `max` | requested; `max` verified as accepted by the proxy |
| `codexproxy` provider | defined in the runner machine's global OpenCode config (not in the repo) | defined inline via `OPENCODE_CONFIG_CONTENT` → CLIProxyAPI `http://127.0.0.1:8317/v1`, Responses API | config was not in the repo |
| Workers | 2 parallel | 1 | single-theorem run |
| Rocq | Rocq 9.1 (from the committed `.vo` version stamps) | Rocq 9.0.1 + MathComp 2.4 (opam switch `prosa-0.6`) | this machine's Prosa environment; committed `.vo` files were rejected as built by 9.1 |
| `implementation/refinements/` | compiled (CoqEAL available) | sources present, not compiled | CoqEAL is not installed; not used by classic case studies |
| coq-lsp / `fcc` | unknown | not installed: `petanque` tool returns an error, runtime AST audit reports `disabled` (default `auto` mode) | `opam install coq-lsp` would rebuild all 14 Rocq/MathComp/Prosa packages of the shared `prosa-0.6` switch (dry run); not needed for proving. The runner's own integrity + `coqc` check still applies |
| ProsaBuddy source | unmodified | `prompt.ts`, `proof-workflow.ts`, `proof-context.ts`, `proof-projection.ts`, `checkpoint.ts`, `coqc.ts`, `coq-session.ts`, `task.ts` patched + `compile-verdict.ts` added (`patches/01-proof-loop-fixes.patch`) | agents looped on read/checkpoint; marker parser blocked lemma dispatch; see "Patches" |
| `setsid` | util-linux `setsid` (Linux) | `.tools/bin/setsid`, a 20-line C shim (`.tools/src/setsid.c`): `setsid()` then `exec`, same pid/process-group semantics | `tool/coq-project.ts` runs every `coqc`/`coqtop`/`coq_session` call as `setsid <cmd>`; macOS has no `setsid`. The first launch failed every Coq call for this reason and was stopped (run 01 in `results/RUNS.md`) |
| Claude Code integration | n/a | `OPENCODE_DISABLE_CLAUDE_CODE=1` | keeps `~/.claude/skills` on this Mac out of the agent's skill list |
| App folder name | `prosabuddy/` (repo root) | `prosabuddy/` (renamed from `opencode/` on 2026-10-07) | clearer name; `run_casestudy_our_minprosa.py` gets one extra skill-dir fallback `ROOT/prosabuddy/.opencode/skill`, because it resolves its fallback directories before reading `OPENCODE_SKILL_SOURCE_DIR` and would otherwise stop at startup |
| `proof.tex` | used when the case directory has one | none for this case in `RTS_Papers` | not available |

## Run

Requires CLIProxyAPI running (`brew services info cliproxyapi`) and `prosa_v06` compiled.

```bash
scripts/run_case_gpt6luna.sh                       # 2005-ECRTS-Lemma3 (default)
scripts/run_case_gpt6luna.sh 2007-RTSS-Theorem2    # any case under datasets_v06/casestudy_v06/
```

Rebuild Prosa: `cd prosa_v06 && eval $(opam env --switch=prosa-0.6 --set-switch) && make -f Makefile.build -j8`
(regenerate `Makefile.build` from `_CoqProject.build` with `rocq makefile -f _CoqProject.build -o Makefile.build`).

## Patches to ProsaBuddy (`patches/01-proof-loop-fixes.patch`)

All source changes, as one diff against `../prosabuddy`; `bun run typecheck` passes. Everything else is unmodified.

**Patch 1: transaction-recovery reminder loop** (`session/prompt.ts`, `tool/checkpoint.ts`, `tool/coqc.ts`, new
`tool/compile-verdict.ts`). `prompt.ts` injects `<proof-edit-transaction-recovery>` into every prover turn while a
recovered transaction has staged edits. Its text always said "read the target .v file through the read tool ... the
controller will reject those state-dependent actions until this staged-revision resynchronization read occurs", even
after the read had been acknowledged (`read.ts` → `acknowledgeStagedRead`; checked by `requiresStagedRead`). The model
kept re-reading (Lemma3 run). A first fix that pointed at `checkpoint` instead produced a checkpoint loop (Theorem2
run 1): when the draft cannot be certified (here a normal-form drift blocker), `validation_pending` stays true and the
same checkpoint result repeats. Now:
- while a read is required, the original text is shown unchanged;
- after the read, the reminder states `staged_read_synchronized: true` and that re-reading does nothing;
- `checkpoint`/`coqc` record their last verdict per session (source hash, status, blockers). If the current staged
  revision was not compiled yet, the reminder asks for one checkpoint; if it was, the reminder repeats that verdict and
  says recompiling unchanged source cannot clear `validation_pending`, so the next step must be an edit or the allowed
  `proof_plan` repair.

**Patch 2: cross-step repetition guard** (`session/prompt.ts`). OpenCode's `doom_loop` check only compares tool
calls within one assistant message, so one identical call per step is never caught. When the last 8 completed tool
calls are the same tool on the same file with no edit, plan revision or delegation in between, a `<repetition-guard>`
notice tells the agent to change state (edit, repair the plan, delegate) or state its blocker.

**Patch 3: JSON-style lists in region markers** (`session/proof-workflow.ts`, `attrList`). `depends_on: []`
(the shape `proof_plan` itself returns) was parsed as one dependency named `"[]"` (and `[a, b]` as `"[a"`, `"b]"`), so the
materialization review reported a dependency mismatch the model could not fix. Brackets/quotes are now stripped and
`[]`, `-`, `n/a` count as empty like `none`.

**Patch 4: multi-word contract values inside the begin marker** (`session/proof-workflow.ts`, `parseRegions`).
`parseAttributes` reads every `key: value` as a single token, so `normal_form: forall j0, arrives_in ... -> ...` written
in the marker parsed as `"forall"`, and marker attributes override the (correctly parsed) contract comment. The review
then always reported "target normal form differs from the accepted plan", the scheduler never dispatched a `lemma`, and
the single plan repair was spent (run 05). Contract fields in the marker now take the text up to the next known key;
identifier attributes (`owner`, `admit_id`, `kind`, `target`) are parsed as before. Verified on run 05's markers:
old `"forall"` / `["[]"]`, new = the accepted plan's normal form / `[]`.

**Patch 5: lemma `coq_session` false desync** (`tool/coq-session.ts`, `expectedGoalMatches`). A lemma worker's
region session checks that the Coq goal at the region entry equals the assigned goal, by exact text after whitespace
normalization. Rocq prints binders with types (`forall j0 : Job, ...`) while assignments come from source text
(`forall j0, ...`), so the session was flagged `session_state_desync` and every tactic was blocked (run 06). If the
strict check fails, the comparison is repeated with binder type annotations erased (`forall x : T,`,
`forall (x y : T) (z : U),` → `forall x y z,`; also `exists`, `fun`). Verified on run 06's assignment and the goal
Rocq prints there (strict: false, patched: true); a goal with a different conclusion is still rejected.

**Patch 6: premature `Qed.` hint** (`session/prompt.ts`). In run 07 the prover changed the theorem terminator to
`Qed.` while a lemma-owned region still contained `admit.`. Every compile then failed at the terminator, so the draft
could never earn the compiler receipt the scheduler needs before dispatching that region. When the last compile of the
current revision failed at the terminator ("Attempt to ...") and the staged source still contains `admit.`, the
recovery reminder now says to restore `Admitted.` and checkpoint once. Observed working: the prover restored
`Admitted.` and the next checkpoint was `decomposition_ready`.

**Patch 7: certify a compiling, plan-matched skeleton** (`tool/checkpoint.ts`, `tool/coqc.ts`). Even with
`decomposition_ready` / `terminal_ready: true`, a compile that is not *new* progress (e.g. the first compile in a fresh
recovery session is recorded as the baseline) left `validation_pending` true, and `planNextSubtask` refuses to dispatch
lemma work while validation is pending, so the remaining region was never dispatched. Such a compile of the exact
staged revision is now recorded as a `structural` certificate for that revision (`markCertifiedRecovery`, which
already rejects a stale source). Nothing is written to the workspace file by this.

**Patch 8: `H_` target-name tolerance** (`session/proof-workflow.ts`, `resolveTargetName`). The marker said
`target: all_same_task_interference_lt` while the exported statement was `have H_all_same_task_interference_lt : ...`;
the exact lookup failed, and every lemma dispatch was rejected with "must wrap exported target statement ...", which
the model did not decode (3 rejections in run 07). If the exact name is not declared inside the region, the unique
`H_`-prefix variant that is declared there is accepted; otherwise behavior is unchanged.

**Patch 9: workspace-relative `File:` paths** (`session/proof-context.ts`, `session/proof-projection.ts`). The live
proof context printed the target as `path.relative(Instance.worktree, file)`. Run workspaces live inside the
`TranslationProof` git repo, so this showed `replicate-prosa-buddy/results/.../Theorem3.v`; the model joined it onto an
absolute prefix (`.../replicate-prosa-buddy/replicate-prosa-buddy/...`), `checkpoint` rejected the path, and in run 07
a lemma worker escalated for that reason. Paths are now relative to the workspace (`Instance.directory`), i.e.
`Theorem3.v`. (In the original setup, outside any git repo, the worktree is `/` and the same code printed
`home/junyi/...`.)

**Patch 10: empty optional fields in `proof_result`** (`tool/task.ts`). A lemma returned a correct `solved` result
with `"escalation_type": ""`; the enum check failed and the whole `proof_result` was marked invalid (the region was still
accepted through its compiler certificate in that run, but the structured result was discarded). Empty-string or
`null` values of the optional fields `escalation_type`, `remodel_request`, `attempt_report` are now treated as absent;
an `escalate` result still needs a valid `escalation_type`.

**Patch 11: tolerate a restated region target after the plan is locked** (`session/proof-workflow.ts`, materialization
review; separate diff `patches/02-plan-normal-form-tolerance.patch`, 2026-10-07). The review compared each delegated
region's `normal_form` contract with the accepted plan's text (whitespace/case-insensitive). After the plan is locked,
a prover that restates a target (2005-ECRTS-Lemma3 run `20261007_143032`: `num_cpus * backlogged ...` became
`num_cpus * (if backlogged ... then 1 else 0)`) kept the review `drifted` for 33 checkpoints; no `lemma` was ever
dispatched and the run ended at the retry limit (8 attempts, 50.6M tokens). Now a differing `normal_form` is accepted
when the region's exported `have` statement matches its own `normal_form` (the existing `targetShapeMatches` check);
otherwise the mismatch is reported as before. Each acceptance is logged (`patch 11: accepted region normal_form ...`).
Soundness is unchanged: regions must compile, and success still requires `Qed.`, no admits/axioms and a clean `coqc`.

**Patch 11b: formatting-insensitive normal-form comparison + informative blocker** (new `session/normal-form.ts`,
`session/proof-workflow.ts`; diff `patches/03-normal-form-formatting.patch`, 2026-10-07). A closer look at run
`20261007_143032` showed that the plan and the region used the same statement; the texts differed only in doubled
backslashes (`\\sum`, a JSON double-escaping slip in the model's edit that the compiler never sees inside the contract
comment) and redundant outer parentheses, and the blocker message did not say what differed (the prover then changed
the right-hand side, which was not the problem). Now: (1) the review treats plan and region normal forms as equal when
they differ only in doubled backslashes, parentheses, spacing, case, binder type annotations (`forall t : time,` vs
`forall t,`) or a final period; (2) `normalizeTargetShape` (have-statement vs contract, used by the lemma locality gate)
also collapses doubled backslashes; (3) a remaining mismatch reports the first differing fragment of plan vs region.
Patch 11's acceptance of a self-consistent restated target is kept as the next fallback. Known limit: ignoring
parentheses could equate `a * (b + c)` with `a * b + c`; this only affects lemma dispatch, never proof checking.

**Patch 12: formatting-insensitive lemma session entry check** (`tool/coq-session.ts`, `expectedGoalMatches`; diff
`patches/04-session-goal-formatting.patch`, 2026-10-07). Rocq prints goals without redundant parentheses (the body of
`\\sum_(cpu < num_cpus) (a && b)` is printed as `a && b`), while lemma assignments carry the source text. The session's
entry check compared them modulo whitespace and binder types only (patch 5), so in Lemma3 run `20261007_165915` every
lemma session reported `session_state_desync`, all tactics were blocked and all three lemmas escalated. The check now
falls back to patch 11b's `NormalFormText.sameModuloFormatting` (parentheses, doubled backslashes, binder types,
spacing). Verified on the real assignment text vs the goal Rocq prints at that region; a goal with `*` changed to `+`
still mismatches.

**Patch 13: show the real Rocq error in `coq_session` feedback** (`tool/coq-session.ts`, `classify`; diff
`patches/05-session-error-summary.patch`, 2026-10-07). The step feedback summary was the first 3 non-empty stderr lines.
With Prosa's imports, Rocq 9.0.1 + MathComp 2.4 print 16 notation warnings (~50 lines) before any error, so every
failed tactic was reported as the first notation warning (kind `environment_problem`) and the actual error was hidden
(Lemma3 run `20261007_165915`: `move=> t cpu BACK.` failed with `Error: No assumption in (...)` on stderr line 53 of 58;
the lemma only saw the warning). Warning blocks are now dropped and the summary starts at the first `Error` (with its
`File ... line ...` location, up to 8 lines). The feedback kinds are unchanged.

**Patch 14: ignore stale region dependencies** (`session/proof-workflow.ts`, materialization review; diff
`patches/06-stale-dependency-tolerance.patch`, 2026-10-08). In 2015-BOOK-Lemma18.1 run `20261008_131220` an accepted
plan repair removed node `pointwise_cap`, but the `fp_aggregate`/`gn_aggregate` region markers kept
`depends_on: pointwise_cap`. Every checkpoint reported a dependency mismatch, no lemma was dispatched, and five
attempts used five retries in ~30 minutes. Dependencies naming a step that is not in the current plan are now
ignored (logged as `patch 14: ...`); mismatches between existing plan steps are still reported.

**Patch 15: strict statement comparison; patch 11 withdrawn** (`session/normal-form.ts` `statement`/`sameStatement`,
`session/proof-workflow.ts` materialization review; diff `patches/07-strict-statement-review.patch`, 2026-10-08
21:22). In the 2026-10-08 four-agent fleet, patch 11 accepted real statement changes: 2015-BOOK-Lemma18.1
`pointwise_cap` bounded `interference_bound_generic` instead of the planned `total_interference_bound`, and later
lemmas escalated because that cap did not cover the planned function. Patch 11b dropped all parentheses, so it
would also equate `a - (b - c)` with `a - b - c`. The review now accepts a region normal_form only when it equals
the plan's after removing formatting: doubled backslashes, spacing, binder types, a final period, and parentheses
around one atom, around the whole text, or around a whole side of a relation when nothing inside binds more
loosely. Bound variables (forall/exists/fun and MathComp bigops) are renamed canonically, so Rocq's `k` -> `k0`
renaming no longer counts as a change. A region that states the plan's conclusion with its leading binders and
premises already introduced (`forall t, P t -> Q t` vs `Q t`, same names) is also accepted (added 22:11 after
2009-RTSS-Lemma3 `clipped_sum_bound`). When the plan's normal_form is English prose rather than Coq ("for each
admissible t and pair in hp_bounds, ...", "response time of j > R"; detected by `looksLikeProse`), no Coq text
can equal it. Such nodes fall back to patch 11's own-target-shape check (added 22:23), and so do region contracts
that arrive truncated because only the first line of a multi-line `normal_form:` marker is parsed (`looksTruncated`,
added 23:01). Everything else is reported as drift with the first normalized difference.
Former patch 11 acceptances are logged as `patch 15: rejected ...`. Live-goal matching in `coq_session` (patch 12)
still uses the looser comparison, because Rocq drops parentheses when it prints goals.

**Patch 16: AST audit load paths for fcc** (`tool/coq-ast-audit.ts`, `fccLoadpathFlags`; diff
`patches/08-ast-audit-fcc-loadpath.patch`, 2026-10-08 21:49). The final-gate AST audit passed the coqc-style
`_CoqProject` flags (`-R prosa prosa`) to coq-lsp 0.2.5's `fcc`, which accepts only `-R DIR,LP`. Every audit therefore
failed with `AST_AUDIT_EXECUTION_FAILED` ("option '-R': invalid value 'prosa', missing a ',' separator"), and complete
proofs were rejected and never committed: 5 times in Lemma3 run `20261007_191146`, and in 2015-BOOK-Lemma18.1 run
`20261008_174953`. For Lemma18.1, the complete revision 115 was recovered from the session database and verified
independently (`results/Lemma18_1_proved_pc_20261008.v`). Load-path pairs are now joined as `-R DIR,LP` / `-Q DIR,LP`.

Patches 1-6 were active in the successful Theorem3 attempt; patches 7-10 fix failures observed in run 07 and were
written while its final attempt was already running, so they have not yet been exercised in a successful run.

## Results

Full run history, folders and token counts: [`results/RUNS.md`](results/RUNS.md).

| Case | Result |
|---|---|
| 2005-ECRTS-Lemma3 | **Not proved** (run 02, unpatched code). Prover built a one-region skeleton; `lemma` escalated; the prover then looped on re-reading the file (the transaction-recovery reminder bug fixed by patch 1), and after a resume the plan-repair guards locked further replanning. Stopped at retry 4/8, ~23M tokens. |
| 2007-RTSS-Theorem2 | **Proved** (run 04, patched code; 1 attempt, 1.2M tokens, 15 min). Verified independently: clean `coqc`, `Print Assumptions` → "Closed under the global context", text outside `Proof. … Qed.` unchanged, workspace Prosa identical to `prosa_v06`. **Caveat:** the theorem is a restatement of Prosa's `Interference.task_interference_le_workload` (same type after `End Section`; the case-study hypotheses are unused), and the proof is `exact: task_interference_le_workload tsk t1 t2` inside the required region scaffolding. It shows the pipeline works end to end, not non-trivial proving. Neither patch notice fired in this run. |
| 2007-RTSS-Theorem3 | **Proved** (run 07, 6 attempts, 93 min, 27.8M tokens; proof copied to `results/Theorem3_proved.v`). Verified independently: clean `coqc`, `Print Assumptions` → "Closed under the global context", text outside `Proof. … Qed.` unchanged. 162-line proof: a `lemma` agent proved the region "every job of `tsk` has interference < R − cost + 1" (forward direction of the case study's hypothesis `Lemma1` + `j_has_max_interference`), and the prover proved the response-time bound by counting service and backlog over the window (`completion_monotonic`, `not_scheduled_no_service`, `service_before_arrival_eq_service_during`). The theorem is conditional on the case study's own hypotheses `Lemma1` and `j_has_max_interference` (stated as `Hypothesis` in the input file). The successful attempt ran with patches 1-6; patches 7-10 were written during that attempt and are not yet exercised in a successful run. Earlier runs 05 (parser deadlock) and 06 (false `coq_session` desync) led to patches 3-5. |

Interventions during the history above: run 01 was stopped because of the missing `setsid`; run 02's stuck
invocation was terminated and the run continued with the original resume mechanism (`--resume-run-dir
--fresh-session-on-resume`), then stopped during a repeat of the loop; run 03 was stopped during the checkpoint loop.
