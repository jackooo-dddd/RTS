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
| `opencode/` | The ProsaBuddy app (OpenCode fork): root manifests + `bun.lock`, `packages/{opencode,plugin,sdk,util,script}` (no `test/`, Dockerfile, dev docs) | `prosabuddy/` |
| `opencode/.opencode/` | Project agents, the 8 proof skills, commands, custom Coq tools, `opencode.jsonc` (no translation glossary/themes) | `prosabuddy/.opencode/` |
| `opencode/scripts/` | AST validator used by the runtime AST audit (`coq-ast-audit.ts` resolves `<app>/scripts`) | `prosabuddy/scripts/` |
| `scripts/` | Experiment runner and its support files, in the layout the runner expects (`ROOT/scripts`) | `prosabuddy/scripts/scripts_junyi/` |
| `scripts/run_ecrts_lemma3_rebuttal.sh` | The original launcher for this theorem, unchanged, for reference | same |
| `scripts/opencode_runner_config.env` | Original runner settings; only `/home/junyi` paths replaced, `PARALLEL=1` | rewritten |
| `scripts/run_case_gpt6luna.sh` | Launcher for this replication (mirrors the original launcher) | new |
| `prosa_v06/` | Prosa v0.6 (`analysis behavior implementation model results util`) + ProsaBuddy's `classic`, `.v` sources compiled here with Rocq 9.0.1 | `prosabuddy/prosaworkspace/` (symlinks resolved) |
| `datasets_v06/casestudy_v06/<case>/` | Case-study inputs (`.v` + paper PDF): `2005-ECRTS-Lemma3`, `2007-RTSS-Theorem2`, `2007-RTSS-Theorem3` | `../RTS_Papers/<case>/` |
| `patches/` | Every change made to ProsaBuddy source, as unified diffs against `../prosabuddy` | new |
| `results/` | Run outputs: staged workspace, logs, request traces, per-attempt records (git-ignored) | generated |
| `.tools/bin/bun` | Bun 1.3.10, the version ProsaBuddy pins (`packageManager`) | GitHub release |
| `gptAPITest/` | CLIProxyAPI smoke test; its `.env` holds the local proxy URL + key used by the launcher | earlier setup |

## Same as the original experiment

- Agents: the built-in ProsaBuddy agents `prover` (entry agent) → `lemma`, `fixer`, `diagnoser`, `explorer`,
  `whole-lemma`, plus the project agents in `.opencode/agent/`. Prompts are the unmodified source files.
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
