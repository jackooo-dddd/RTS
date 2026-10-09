# LeanBuddy migration log

Implementation log for [AGENT_PROMPT.md](AGENT_PROMPT.md). Branch `leanbuddy-migration`. Newest entries at the
bottom of each section. Scratch and build material lives outside git in `~/leanbuddy-work/`.

## Where the work runs (from 2026-10-09 19:20, user request)

All builds, tests, the spike and later runs execute on the **CityU PC** (WSL Ubuntu, 28 cores, 47 GB; `ssh cityu-wsl`):

| Item | PC path |
|---|---|
| Git clone (branch `leanbuddy-migration`) | `~/research/leanbuddy-migration/` (separate from the fleet's `~/research/RTS`, which is not touched) |
| Lean package master build (no `Solutions/`) | `~/research/leanbuddy-work/lean-prosa-v06-master/` (`build-master.sh`, 14 cores, `nice 10`) |
| Pantograph `92d4818` (0.3.19) | `~/research/leanbuddy-work/Pantograph/` |
| Pristine-tree baseline worktree | `~/research/leanbuddy-work/baseline-11856eeb/` |
| Logs | `~/research/logs/leanbuddy-*.log` |

Files are edited in the Mac checkout (git authority) and mirrored with `~/leanbuddy-sync/sync-to-pc.sh` (rsync,
no `node_modules`); commits are made on the Mac. The Mac's `~/leanbuddy-work/` (partial build, stopped at 269
modules) is no longer used.

## Phase 0 — workspace baseline (2026-10-09, Mac: Apple M4, 16 GB, macOS 15 / Darwin 24.6)

- `leanbuddy/` = copy of `prosabuddy-rocq/` (706 files; `BASELINE.md` dropped, `.gitignore` kept).
- `bun install` with Bun 1.3.10 (`replicate-prosa-buddy/.tools/bin/bun`, arm64): 1,678 packages.
- `bun run typecheck` (root, before any change): **4/4 packages pass** (5 s).
- `bun test --timeout 30000` in `packages/opencode` (before any change): **1,494 pass, 9 skip, 28 fail**, 1,531 tests
  in 103 files, 405 s. Log: `~/leanbuddy-work/baseline-test.log`.

Pre-existing failures (all 28 are environmental; none is a migration signal):

| Cause | Tests | Count |
|---|---|---|
| No Rocq toolchain on the Mac (`coqc`, `coqtop`, `fcc` absent) | `coq AST audit` ×3; `tool.task recursive proof agents` ×3; `tool.proof_plan bounded semantic review` ×3; `tool.proof-premise-audit` ×5; `proof edit transaction` ×3; `session.proof-workflow lemma scheduling > checkpoint scaffold compiles…` ×1; `tool.bash > allows read-only shell commands that mention the active transaction file` ×1 (exit 127) | 19 |
| Network (remote download / provider stream) | `Discovery.pull` ×4 (skill download from a URL); `session.llm.stream` ×4 (30 s timeouts) | 8 |
| Error classification of a socket reset | `session.message-v2.fromError > converts ECONNRESET socket errors to retryable APIError` | 1 |

(The PC baseline of the pristine tree was 129 pass / 9 fail on a subset with 5 s timeouts; the Mac run is the full
suite with 30 s timeouts.) The Rocq-dependent tests belong to modules that Phases 2–4 replace; their Lean
replacements must pass.

## Note status

`todo` / `done` / `deviated` (deviations are explained in the *Deviations* section).

| # | Note | Status | Phase | Commit / remark |
|---|---|---|---|---|
| 1 | [BACKEND_DECISION.md](migration-suggestions/BACKEND_DECISION.md) | todo | 1, 4 | |
| 2 | [gap-revisions/01-prompt.ts-revision.md](migration-suggestions/gap-revisions/01-prompt.ts-revision.md) | todo | 3–8 | |
| 3 | [gap-revisions/02-system-prompts/coqprover.txt-revision.md](migration-suggestions/gap-revisions/02-system-prompts/coqprover.txt-revision.md) | todo | 3–8 | |
| 4 | [gap-revisions/02-system-prompts/proof-workflow-principles.txt-revision.md](migration-suggestions/gap-revisions/02-system-prompts/proof-workflow-principles.txt-revision.md) | todo | 3–8 | |
| 5 | [gap-revisions/02-system-prompts/system.ts-revision.md](migration-suggestions/gap-revisions/02-system-prompts/system.ts-revision.md) | todo | 3–8 | |
| 6 | [gap-revisions/03-small-source-files/agent.ts-revision.md](migration-suggestions/gap-revisions/03-small-source-files/agent.ts-revision.md) | todo | 3–8 | |
| 7 | [gap-revisions/03-small-source-files/compaction.ts-revision.md](migration-suggestions/gap-revisions/03-small-source-files/compaction.ts-revision.md) | todo | 3–8 | |
| 8 | [gap-revisions/03-small-source-files/message-v2.ts-revision.md](migration-suggestions/gap-revisions/03-small-source-files/message-v2.ts-revision.md) | todo | 3–8 | |
| 9 | [gap-revisions/03-small-source-files/run.ts-revision.md](migration-suggestions/gap-revisions/03-small-source-files/run.ts-revision.md) | todo | 3–8 | |
| 10 | [gap-revisions/03-small-source-files/tui-dialog-status.tsx-revision.md](migration-suggestions/gap-revisions/03-small-source-files/tui-dialog-status.tsx-revision.md) | todo | 3–8 | |
| 11 | [gap-revisions/03-small-source-files/tui-lsp.ts-revision.md](migration-suggestions/gap-revisions/03-small-source-files/tui-lsp.ts-revision.md) | todo | 3–8 | |
| 12 | [gap-revisions/03-small-source-files/tui-sidebar.tsx-revision.md](migration-suggestions/gap-revisions/03-small-source-files/tui-sidebar.tsx-revision.md) | todo | 3–8 | |
| 13 | [gap-revisions/03-small-source-files/tui-sync.tsx-revision.md](migration-suggestions/gap-revisions/03-small-source-files/tui-sync.tsx-revision.md) | todo | 3–8 | |
| 14 | [gap-revisions/04-audit-backend/checkpoint.ts-audit-revision.md](migration-suggestions/gap-revisions/04-audit-backend/checkpoint.ts-audit-revision.md) | todo | 3 | |
| 15 | [gap-revisions/04-audit-backend/coq-ast-audit.ts-revision.md](migration-suggestions/gap-revisions/04-audit-backend/coq-ast-audit.ts-revision.md) | todo | 3 | |
| 16 | [gap-revisions/04-audit-backend/coqc.ts-audit-revision.md](migration-suggestions/gap-revisions/04-audit-backend/coqc.ts-audit-revision.md) | todo | 3 | |
| 17 | [gap-revisions/04-audit-backend/removed-files.md](migration-suggestions/gap-revisions/04-audit-backend/removed-files.md) | todo | 3 | |
| 18 | [gap-revisions/04-audit-backend/task.ts-audit-revision.md](migration-suggestions/gap-revisions/04-audit-backend/task.ts-audit-revision.md) | todo | 3 | |
| 19 | [gap-revisions/04-audit-backend/validate_classified_ast.py-revision.md](migration-suggestions/gap-revisions/04-audit-backend/validate_classified_ast.py-revision.md) | todo | 3 | |
| 20 | [gap-revisions/05-benchmark-runner/opencode_our_local.sh-revision.md](migration-suggestions/gap-revisions/05-benchmark-runner/opencode_our_local.sh-revision.md) | todo | 8 | |
| 21 | [gap-revisions/05-benchmark-runner/opencode_our_prompt.md-revision.md](migration-suggestions/gap-revisions/05-benchmark-runner/opencode_our_prompt.md-revision.md) | todo | 8 | |
| 22 | [gap-revisions/05-benchmark-runner/opencode_runner_config-revision.md](migration-suggestions/gap-revisions/05-benchmark-runner/opencode_runner_config-revision.md) | todo | 8 | |
| 23 | [gap-revisions/05-benchmark-runner/run_casestudy_opencode_minprosa.py-revision.md](migration-suggestions/gap-revisions/05-benchmark-runner/run_casestudy_opencode_minprosa.py-revision.md) | todo | 8 | |
| 24 | [gap-revisions/05-benchmark-runner/run_casestudy_our_minprosa.py-revision.md](migration-suggestions/gap-revisions/05-benchmark-runner/run_casestudy_our_minprosa.py-revision.md) | todo | 8 | |
| 25 | [gap-revisions/07-tests/session__message-v2.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/session__message-v2.test.ts-revision.md) | todo | 3–5 | |
| 26 | [gap-revisions/07-tests/session__prompt.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/session__prompt.test.ts-revision.md) | todo | 3–5 | |
| 27 | [gap-revisions/07-tests/session__proof-edit-transaction.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/session__proof-edit-transaction.test.ts-revision.md) | todo | 3–5 | |
| 28 | [gap-revisions/07-tests/session__proof-projection.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/session__proof-projection.test.ts-revision.md) | todo | 3–5 | |
| 29 | [gap-revisions/07-tests/session__proof-route-ledger.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/session__proof-route-ledger.test.ts-revision.md) | todo | 3–5 | |
| 30 | [gap-revisions/07-tests/session__proof-workflow.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/session__proof-workflow.test.ts-revision.md) | todo | 3–5 | |
| 31 | [gap-revisions/07-tests/session__system.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/session__system.test.ts-revision.md) | todo | 3–5 | |
| 32 | [gap-revisions/07-tests/session__trace.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/session__trace.test.ts-revision.md) | todo | 3–5 | |
| 33 | [gap-revisions/07-tests/test_opencode_runner_config.py-revision.md](migration-suggestions/gap-revisions/07-tests/test_opencode_runner_config.py-revision.md) | todo | 3–5 | |
| 34 | [gap-revisions/07-tests/test_run_casestudy_continuation_prompt.py-revision.md](migration-suggestions/gap-revisions/07-tests/test_run_casestudy_continuation_prompt.py-revision.md) | todo | 3–5 | |
| 35 | [gap-revisions/07-tests/test_run_casestudy_decompose.py-revision.md](migration-suggestions/gap-revisions/07-tests/test_run_casestudy_decompose.py-revision.md) | todo | 3–5 | |
| 36 | [gap-revisions/07-tests/tool__apply_patch.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/tool__apply_patch.test.ts-revision.md) | todo | 3–5 | |
| 37 | [gap-revisions/07-tests/tool__bash.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/tool__bash.test.ts-revision.md) | todo | 3–5 | |
| 38 | [gap-revisions/07-tests/tool__coq-ast-audit.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/tool__coq-ast-audit.test.ts-revision.md) | todo | 3–5 | |
| 39 | [gap-revisions/07-tests/tool__coq-diagnostics.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/tool__coq-diagnostics.test.ts-revision.md) | todo | 3–5 | |
| 40 | [gap-revisions/07-tests/tool__coq-project.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/tool__coq-project.test.ts-revision.md) | todo | 3–5 | |
| 41 | [gap-revisions/07-tests/tool__coq-session.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/tool__coq-session.test.ts-revision.md) | todo | 3–5 | |
| 42 | [gap-revisions/07-tests/tool__coq-skill-hints.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/tool__coq-skill-hints.test.ts-revision.md) | todo | 3–5 | |
| 43 | [gap-revisions/07-tests/tool__edit.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/tool__edit.test.ts-revision.md) | todo | 3–5 | |
| 44 | [gap-revisions/07-tests/tool__grep.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/tool__grep.test.ts-revision.md) | todo | 3–5 | |
| 45 | [gap-revisions/07-tests/tool__proof-premise-audit.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/tool__proof-premise-audit.test.ts-revision.md) | todo | 3–5 | |
| 46 | [gap-revisions/07-tests/tool__proof-review.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/tool__proof-review.test.ts-revision.md) | todo | 3–5 | |
| 47 | [gap-revisions/07-tests/tool__proof-schema.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/tool__proof-schema.test.ts-revision.md) | todo | 3–5 | |
| 48 | [gap-revisions/07-tests/tool__read.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/tool__read.test.ts-revision.md) | todo | 3–5 | |
| 49 | [gap-revisions/07-tests/tool__task.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/tool__task.test.ts-revision.md) | todo | 3–5 | |
| 50 | [gap-revisions/07-tests/tool__write.test.ts-revision.md](migration-suggestions/gap-revisions/07-tests/tool__write.test.ts-revision.md) | todo | 3–5 | |
| 51 | [known-problem-fixes/lean_session-equivalence.md](migration-suggestions/known-problem-fixes/lean_session-equivalence.md) | todo | 4 | |
| 52 | [known-problem-fixes/lemma.txt-fixes.md](migration-suggestions/known-problem-fixes/lemma.txt-fixes.md) | todo | 5 | |
| 53 | [known-problem-fixes/prompt.ts-fixes.md](migration-suggestions/known-problem-fixes/prompt.ts-fixes.md) | todo | 5 | |
| 54 | [known-problem-fixes/proof-context.ts-fixes.md](migration-suggestions/known-problem-fixes/proof-context.ts-fixes.md) | todo | 5 | |
| 55 | [known-problem-fixes/proof-plan.ts-fixes.md](migration-suggestions/known-problem-fixes/proof-plan.ts-fixes.md) | todo | 5 | |
| 56 | [known-problem-fixes/proof-projection.ts-fixes.md](migration-suggestions/known-problem-fixes/proof-projection.ts-fixes.md) | todo | 5 | |
| 57 | [known-problem-fixes/proof-schema.ts-fixes.md](migration-suggestions/known-problem-fixes/proof-schema.ts-fixes.md) | todo | 5 | |
| 58 | [known-problem-fixes/proof-workflow.ts-fixes.md](migration-suggestions/known-problem-fixes/proof-workflow.ts-fixes.md) | todo | 5 | |
| 59 | [known-problem-fixes/prover.txt-fixes.md](migration-suggestions/known-problem-fixes/prover.txt-fixes.md) | todo | 5 | |
| 60 | [known-problem-fixes/provider.ts-fixes.md](migration-suggestions/known-problem-fixes/provider.ts-fixes.md) | todo | 5 | |
| 61 | [known-problem-fixes/whole-lemma.txt-fixes.md](migration-suggestions/known-problem-fixes/whole-lemma.txt-fixes.md) | todo | 5 | |
| 62 | [prompt-advices/prompt_revision.md](migration-suggestions/prompt-advices/prompt_revision.md) | todo | 5 | |
| 63 | [skill-advices/count-bridging/SKILL.md](migration-suggestions/skill-advices/count-bridging/SKILL.md) | todo | 5 | |
| 64 | [skill-advices/failure-signature/SKILL.md](migration-suggestions/skill-advices/failure-signature/SKILL.md) | todo | 5 | |
| 65 | [skill-advices/goal/SKILL.md](migration-suggestions/skill-advices/goal/SKILL.md) | todo | 5 | |
| 66 | [skill-advices/guide/SKILL.md](migration-suggestions/skill-advices/guide/SKILL.md) | todo | 5 | |
| 67 | [skill-advices/math/SKILL.md](migration-suggestions/skill-advices/math/SKILL.md) | todo | 5 | |
| 68 | [skill-advices/parameter/SKILL.md](migration-suggestions/skill-advices/parameter/SKILL.md) | todo | 5 | |
| 69 | [skill-advices/prosabuddy-guard-recovery/SKILL.md](migration-suggestions/skill-advices/prosabuddy-guard-recovery/SKILL.md) | todo | 5 | |
| 70 | [skill-advices/tactics/SKILL.md](migration-suggestions/skill-advices/tactics/SKILL.md) | todo | 5 | |
| 71 | [tools-advices/01-core-tools/checkpoint-revision.md](migration-suggestions/tools-advices/01-core-tools/checkpoint-revision.md) | todo | 2/5 | |
| 72 | [tools-advices/01-core-tools/coq-session-revision.md](migration-suggestions/tools-advices/01-core-tools/coq-session-revision.md) | todo | 2/5 | |
| 73 | [tools-advices/01-core-tools/coqc-revision.md](migration-suggestions/tools-advices/01-core-tools/coqc-revision.md) | todo | 2/5 | |
| 74 | [tools-advices/01-core-tools/coqtop-revision.md](migration-suggestions/tools-advices/01-core-tools/coqtop-revision.md) | todo | 2/5 | |
| 75 | [tools-advices/01-core-tools/petanque-revision.md](migration-suggestions/tools-advices/01-core-tools/petanque-revision.md) | todo | 2/5 | |
| 76 | [tools-advices/01-core-tools/proof-plan-revision.md](migration-suggestions/tools-advices/01-core-tools/proof-plan-revision.md) | todo | 2/5 | |
| 77 | [tools-advices/02-adapted-tools/apply_patch-revision.md](migration-suggestions/tools-advices/02-adapted-tools/apply_patch-revision.md) | todo | 2/5 | |
| 78 | [tools-advices/02-adapted-tools/bash-revision.md](migration-suggestions/tools-advices/02-adapted-tools/bash-revision.md) | todo | 2/5 | |
| 79 | [tools-advices/02-adapted-tools/edit-revision.md](migration-suggestions/tools-advices/02-adapted-tools/edit-revision.md) | todo | 2/5 | |
| 80 | [tools-advices/02-adapted-tools/lsp-revision.md](migration-suggestions/tools-advices/02-adapted-tools/lsp-revision.md) | todo | 2/5 | |
| 81 | [tools-advices/02-adapted-tools/multiedit-revision.md](migration-suggestions/tools-advices/02-adapted-tools/multiedit-revision.md) | todo | 2/5 | |
| 82 | [tools-advices/02-adapted-tools/read-revision.md](migration-suggestions/tools-advices/02-adapted-tools/read-revision.md) | todo | 2/5 | |
| 83 | [tools-advices/02-adapted-tools/task-revision.md](migration-suggestions/tools-advices/02-adapted-tools/task-revision.md) | todo | 2/5 | |
| 84 | [tools-advices/02-adapted-tools/write-revision.md](migration-suggestions/tools-advices/02-adapted-tools/write-revision.md) | todo | 2/5 | |
| 85 | [tools-advices/03-custom-tools/coq-check-revision.md](migration-suggestions/tools-advices/03-custom-tools/coq-check-revision.md) | todo | 2/5 | |
| 86 | [tools-advices/04-helper-modules/coq-ast-audit-revision.md](migration-suggestions/tools-advices/04-helper-modules/coq-ast-audit-revision.md) | todo | 2/5 | |
| 87 | [tools-advices/04-helper-modules/coq-diagnostics-revision.md](migration-suggestions/tools-advices/04-helper-modules/coq-diagnostics-revision.md) | todo | 2/5 | |
| 88 | [tools-advices/04-helper-modules/coq-project-revision.md](migration-suggestions/tools-advices/04-helper-modules/coq-project-revision.md) | todo | 2/5 | |
| 89 | [tools-advices/04-helper-modules/coq-skill-hints-revision.md](migration-suggestions/tools-advices/04-helper-modules/coq-skill-hints-revision.md) | todo | 2/5 | |
| 90 | [tools-advices/04-helper-modules/coq-style-guard-revision.md](migration-suggestions/tools-advices/04-helper-modules/coq-style-guard-revision.md) | todo | 2/5 | |
| 91 | [tools-advices/04-helper-modules/edit-conflict-guard-revision.md](migration-suggestions/tools-advices/04-helper-modules/edit-conflict-guard-revision.md) | todo | 2/5 | |
| 92 | [tools-advices/04-helper-modules/proof-plan-identifiers-revision.md](migration-suggestions/tools-advices/04-helper-modules/proof-plan-identifiers-revision.md) | todo | 2/5 | |
| 93 | [tools-advices/04-helper-modules/proof-premise-audit-revision.md](migration-suggestions/tools-advices/04-helper-modules/proof-premise-audit-revision.md) | todo | 2/5 | |
| 94 | [tools-advices/04-helper-modules/proof-schema-revision.md](migration-suggestions/tools-advices/04-helper-modules/proof-schema-revision.md) | todo | 2/5 | |
| 95 | [tools-advices/04-helper-modules/registry-revision.md](migration-suggestions/tools-advices/04-helper-modules/registry-revision.md) | todo | 2/5 | |
| 96 | [tools-advices/04-helper-modules/tool-revision.md](migration-suggestions/tools-advices/04-helper-modules/tool-revision.md) | todo | 2/5 | |
| 97 | [tools-advices/05-session-workflow/lemma-assignment-revision.md](migration-suggestions/tools-advices/05-session-workflow/lemma-assignment-revision.md) | todo | 2/5 | |
| 98 | [tools-advices/05-session-workflow/proof-context-revision.md](migration-suggestions/tools-advices/05-session-workflow/proof-context-revision.md) | todo | 2/5 | |
| 99 | [tools-advices/05-session-workflow/proof-edit-transaction-revision.md](migration-suggestions/tools-advices/05-session-workflow/proof-edit-transaction-revision.md) | todo | 2/5 | |
| 100 | [tools-advices/05-session-workflow/proof-policy-revision.md](migration-suggestions/tools-advices/05-session-workflow/proof-policy-revision.md) | todo | 2/5 | |
| 101 | [tools-advices/05-session-workflow/proof-projection-revision.md](migration-suggestions/tools-advices/05-session-workflow/proof-projection-revision.md) | todo | 2/5 | |
| 102 | [tools-advices/05-session-workflow/proof-route-ledger-revision.md](migration-suggestions/tools-advices/05-session-workflow/proof-route-ledger-revision.md) | todo | 2/5 | |
| 103 | [tools-advices/05-session-workflow/proof-workflow-revision.md](migration-suggestions/tools-advices/05-session-workflow/proof-workflow-revision.md) | todo | 2/5 | |
| 104 | [tools-advices/05-session-workflow/session-proof-revision.md](migration-suggestions/tools-advices/05-session-workflow/session-proof-revision.md) | todo | 2/5 | |
| 105 | [tools-advices/06-session-storage/proof-edit-transaction.sql-revision.md](migration-suggestions/tools-advices/06-session-storage/proof-edit-transaction.sql-revision.md) | todo | 2/5 | |
| 106 | [tools-advices/06-session-storage/proof-route-ledger.sql-revision.md](migration-suggestions/tools-advices/06-session-storage/proof-route-ledger.sql-revision.md) | todo | 2/5 | |
| 107 | [tools-advices/06-session-storage/session-proof-workflow.sql-revision.md](migration-suggestions/tools-advices/06-session-storage/session-proof-workflow.sql-revision.md) | todo | 2/5 | |
| 108 | [tools-advices/06-session-storage/session-proof.sql-revision.md](migration-suggestions/tools-advices/06-session-storage/session-proof.sql-revision.md) | todo | 2/5 | |
| 109 | [tools-advices/07-lsp/client-revision.md](migration-suggestions/tools-advices/07-lsp/client-revision.md) | todo | 2/5 | |
| 110 | [tools-advices/07-lsp/index-revision.md](migration-suggestions/tools-advices/07-lsp/index-revision.md) | todo | 2/5 | |
| 111 | [tools-advices/07-lsp/language-revision.md](migration-suggestions/tools-advices/07-lsp/language-revision.md) | todo | 2/5 | |
| 112 | [tools-advices/07-lsp/server-revision.md](migration-suggestions/tools-advices/07-lsp/server-revision.md) | todo | 2/5 | |

## Deviations and note corrections

| # | Note / decision | What the notes say | What was done, and why | Phase |
|---|---|---|---|---|
| V1 | BACKEND_DECISION *First spike* 1 | `frontend.distil` returns goals "in the order of the `sorry`s" | Pantograph 0.3.19 returns them in **reverse** source order (3 regions → h3, h2, h1; `cases` branches → last first; Init-only tests, real-package test pending). Map goals to `admit_id`s by reversed order **and** check each target against the region's declared statement. | 1 |
| V2 | runner revision §4 (bash allow-list `lake env lean`, `lake build`) vs `bash-revision.md` (block compiler calls in bash) | contradictory | bash guard blocks `lean` and `lake build/env/lean/exe/serve/update` and points to `lean_check`/`lean_query`/`lean_session`/`checkpoint` (same design as the Rocq guard, which also refused `coqc` despite the runner's allow-list). The runner's bash allow-list becomes moot (fix in Phase 8). | 2 |
| V3 | (none) | — | `runProcess` wrapped every subprocess in `setsid`, which macOS lacks: every Lean/Lake call would fail on the Mac. It now uses `setsid` when present and `perl -e 'setpgrp; exec'` otherwise (verified: a timed-out process tree is killed completely). | 3 |
| V4 | gap-revisions §4, K9 ("in benchmark mode the gate calls `check.py` itself") | gate = `check.py` | `check.py` reads the solution from disk, but `checkpoint` gates the *staged* (uncommitted) source. The gate runs `check.py` itself when the candidate equals the file on disk, and otherwise the same five checks in TypeScript on a temporary sibling copy (statement probe and `#print axioms` appended). A unit test keeps the token list and allowed axioms identical to `check.py`; the integration test checks the verdicts on the reference and on the `sorry`/`axiom`/`native_decide` variants. The runner's success test stays `check.py` in a fresh verification copy (D14). | 3 |
| V5 | task.ts audit revision (`sorry` allowed "only where the assignment allows a split") | — | the submission stage allows `sorry` in the proof (a `split` result legitimately leaves sub-regions open); "solved" is decided from the source (S26), not by this check. | 3 |
| V6 | D2 (`coq-check` → `lean-check-file` or merge) | prefer merging | the custom tool `.opencode/tool/coq-check.ts` was deleted; `lean_check` covers it. | 2 |
| V7 | `lean_session-equivalence.md` (backstop `expr.echo` fails on holes) | `expr.echo` rejects a hole | it does not (returns a metavariable); the `have _probe` probe does. Token scanner = primary rule. BACKEND_DECISION *Spike results* 5. | 1 |
| V8 | gate test expectation | `native_decide` shows as `Lean.ofReduceBool` | Lean 4.33 adds an auxiliary axiom `<decl>._native.native_decide.ax_…`; both the gate and `check.py` reject it as non-standard. | 1 |
| V10 | BACKEND_DECISION (Pantograph commands) | `env.catalog {}` returns the names | in 0.3.19 `env.catalog` takes a required `filename` and writes one name per line to it (the README example is outdated); the JSON decoder also requires fields that have defaults (`frontend.process` needs `newConstants`, `env.catalog` needs `invertFilter`). The client passes all of them. | 4 |
| V11 | coqtop note (`state`, `eval` commands) | port them | `lean_query` has `check`, `print`, `search` only: goals come from `lean_session`, and `#eval` is forbidden by D4. | 4 |
| V9 | gate (D4) | — | the gate returns `disabled` (`GATE_NOT_LEAN`) for non-`.lean` files instead of judging them (two task tests with Rocq fixtures regressed otherwise; the fixtures are ported in Phase 5). | 3 |
| V12 | proof-workflow fixes K4 | `planNextSubtask`/`suggestNextSubtask` return `{kind: "assignment"} \| {kind: "no_ready_region", …}` | the two functions keep returning an assignment or `undefined` (≈100 test call sites); a separate `schedulerStatus()` computes `{kind: "no_ready_region", reason, required_action, admit_ids}` from the same refreshed state, and `prompt.ts` injects it as `<scheduler-status>` whenever the prover has neither a lemma assignment nor a finalization reminder. Same information, same moment. | 5 |
| V13 | D9 / proof-workflow fixes K2 | amendment unlocked by `needs_preceding_bridge` (or a remodel naming a missing fact) | unlocked by `needs_preceding_bridge`, `needs_uniqueness_bridge` (also a missing bridge fact), `needs_subgoal_remodel` (text detection of "names a missing fact" would be fragile), and by a K8 repeated-escalation block. The old one-shot whole-plan replacement after acceptance is removed (D9: locked except amendments); its three tests were rewritten as amendment tests. | 5 |
| V15 | D10 (comparison "through `lean_session`, i.e. Pantograph") | Pantograph goal state | `tool/lean-statement-check.ts` decides equivalence with the compiler (`lake env lean` on a probe of the staged file): root goal = `theorem probe <binders> : (submitted) ↔ (conclusion) := Iff.rfl` after the file prefix; region target = `have probe : (target) ↔ (normal form) := by first \| (exact Iff.rfl; trace EQ) \| (trace NE; sorry)` inserted before the region (proofs masked to `sorry`). This gives the exact context (opens, section variables, local `intro`s before the region), which a closed Pantograph `goal.start` lacks; one compile covers all regions. Verdicts are cached; the materialization review consults the cache and is redone when new verdicts arrive; checks run at checkpoint/`lean_check`. A plain probe `:= Iff.rfl` was tried first: a failing probe stops the tactic block and drops earlier probes' messages, hence `first`. | 5 |
| V16 | (none) — test harness | — | The PC full suite died in every memory cap: each test `Instance` ran `bun info @opencode-ai/plugin version` (config dependency check, ≈200 MB per process, through the proxy) and 47–134 ran at once. `PackageRegistry.info` is now shared and cached for 10 min per process, and `Config.installDependencies` runs once per directory at a time. Peak bun processes during the suite: 12. The 19:34 OOM incident was most likely this, not Lean. | 5 |
| V14 | D10 / proof-workflow fixes K7 | `kind`/`layer` not compared | additionally, `refresh` copies `kind`/`layer` from the accepted plan node onto each parsed region, so the locality gate (which needs them) works when the marker omits them (D10 marker fields). File values remain only as a fallback for regions with no plan. | 5 |

**Packaging bug found (needs a user decision):** 19 of the 22 `proof.tex` files of `Deliverables/lean-prosa-v06` have
CRLF line endings in the Mac working tree, and `benchmark/frozen_sha256.json` was computed from those bytes, but git
(`core.autocrlf=input`) stores them with LF. Every fresh checkout (the PC clone, any runner copy made from git) fails
`check.py`'s frozen-file check before anything else. Worked around on the PC by copying the Mac's exact bytes for those
19 files into the master copy (all 600 frozen hashes match). Fix options: regenerate the hashes from the LF files, or
add `*.tex -text` to `.gitattributes` and recommit the CRLF bytes.

**Incident (2026-10-09 19:34–19:37, PC):** while the spike's Pantograph REPLs, the gate check's parallel `lake build`
and the Bun test suite ran next to the 4 fleet runs, the kernel OOM killer fired twice; it killed a user `systemd`
process and one `coq-lsp` process (pid 11084, most likely a fleet run's). The fleet runners stayed alive. Since then
every Lean job runs in a memory-capped cgroup (`capped.sh`, verified: an over-limit process is killed inside its own
scope only).

**Needs a user decision (reported, not blocking):** the 130-theorem benchmark's `prosa-theorems/check.py` requires the
task file to differ from the prepared file *only inside the proof* (rule 2), so an added `import` fails there, while
K1's general-case rule lets the gate accept package imports. For those tasks the gate should follow the benchmark
(no header change); proposed handling in Phase 8.

## Phase log

### Phase 1 — done on the PC (19:25–19:55)

- Master build on the PC: `lake exe cache get` + `lake build` (14 cores): **266 s**, 9,279 jobs; `.lake/build` 3.1 GB,
  `.lake/packages` 7.5 GB; staging a run copy (D14) takes 2 s. Pantograph built in 17 s.
- Spike: all checks pass; results and the two changed answers in BACKEND_DECISION *Spike results* (V1 confirmed on the
  real file, V7). Gate end to end: reference PASS, `sorry`/`axiom`/`native_decide`/statement change FAIL (V8).
- PC test baseline of the unmodified tree: **1,501 pass, 9 skip, 21 fail** (the PC has Rocq, `rg` and `setsid`, so
  fewer environmental failures than on the Mac); log `~/research/logs/leanbuddy-test-baseline-pc.log`.

### Phase 1 (Mac attempt, abandoned) — Lean environment and Pantograph

- Master copy `~/leanbuddy-work/lean-prosa-v06-master/` (no `Solutions/`); `lake exe cache get`: 8,690 Mathlib files.
  `lake build` is slow on the Mac: 4–7 parallel `lean` processes of 1.2–3.3 GB each on 16 GB RAM (plus IDEs) swap,
  so each module waits on I/O (~10 % CPU). Timing and `.lake/build` size recorded when it finishes.
- Pantograph `92d4818` built in `~/leanbuddy-work/Pantograph` (`lake build repl`, 69 s; `repl --version` = 0.3.19).
- Smoke tests with `repl Init`: `show` rejects a non-defeq statement and accepts `show _` (holes must be rejected
  before the check); `frontend.distil` on text with an `import` line fails ("invalid 'import' command"); one error
  anywhere aborts `distil`; goal order is reversed (V1). Spike driver: `leanbuddy/scripts/pantograph-spike/`
  (`spike.py`, `pantograph.py`, `gate_check.py`, `stage_copy.sh` = D14 staging prototype).

### Phase 2 — tool surface (D2, D3, D6)

- Tools renamed (files and IDs): `coqc`→`lean_check` (`tool/lean-check.ts`), `coqtop`→`lean_query`
  (`tool/lean-query.ts`), `coq_session`→`lean_session` (`tool/lean-session.ts`); `petanque` deleted (merged, D1);
  custom tool `coq-check` deleted (V6). Their Rocq internals are replaced in Phase 4.
- Every tool-name list updated: registry, agent permissions (prover and explorer now also get read-only `lsp`, D3;
  explorer gets `lean_query`), accepted-plan hard gate (`lean_query`; `coq-proof-dag`/`pdf-read` dropped, GAPS §8),
  passive/active classifiers in `prompt.ts` and `proof-workflow.ts` (petanque branches removed), message cache
  sets, compaction prune list, CLI renderer, validator labels (`checkpoint-coqc`→`checkpoint-lean`), D6 agent
  sets (`coq-prover` removed from `WIDE_PROBE_PROOF_AGENTS`/`WIDE_PROOF_EDIT_AGENTS`), config `tools` entries for
  removed GitHub tools, and tool names inside runtime reminder strings (wording otherwise left for Phase 5).
- bash guard: Lean/Lake compiler calls instead of `coqc`/`coqtop` (V2); `.lean` wildcard detection.

### Phase 3 — final gate (D4, K1, K9)

- New `tool/lean-gate.ts` (`LeanGate`, same public shape as `CoqAstAudit`), `tool/lean-source.ts` (comment
  stripping and token list identical to `check.py`, header, declarations), `tool/lean-project.ts` (Lake root,
  module names, `lake env lean` on a staged copy, `lake build`, diagnostics parser).
- Callers switched: `checkpoint`, `lean_check` (status `final_gate_rejected`), `task` (stage `submission`,
  `<region-check-rejection>`, V5). Vocabulary renamed (`markGateChecked`, `requireGate`, …).
- Deleted: `coq-ast-audit.ts` and its test; `scripts/` OCaml classifier, Python validator, its tests/examples/docs,
  and the elaboration-dump plugin (gap-revisions §4 `removed-files.md`).
- Tests: `test/tool/lean-gate.test.ts` — 11 unit tests (token parity with `check.py`, header, declarations, exterior
  rules incl. K1 imports, reason mapping, axioms parsing) and 3 integration tests on the built package (PC): **14/14
  pass**. Integration found one bug (the probe re-declared `universe u v`; now fresh universe names). `task.test.ts`
  13/13 on the PC after V9.

### Phase 4 — Lean tools on Pantograph (PC)

- `tool/pantograph.ts`: REPL client — one process per (project, import list), started as `lake env <repl> <imports>`,
  serialised requests, wall-clock timeout with kill and restart, RSS watchdog (default 12 GB), error classes
  (`command` vs `backend`; backend errors are tool errors, free under D5), generation counter that invalidates old
  state handles.
- `lean_session` rewritten (see commit message): states from the staged file (header stripped, regions masked to
  `(by sorry)`, text cut after the target), region goal found among the `distil` goals and confirmed with `show`,
  own-goal tracking by name, snapshot/undo by handle, re-open + replay on a source change or restart, expected goal
  by definitional equality, `inspect` by `rfl`, forbidden tactics refused. `LeanEquivalence.equivalentClosed` is the
  D10 service for closed statements.
- `lean_query`: `#check`/`#print` through `frontend.process` on the file up to the target (the file's `open`s apply —
  `Lemma3_05_statement` resolves by its short name), name `search` over the environment catalog (V10, V11).
- `lean_check` and `checkpoint`: the compile step is now `LeanProject.compile` (rebuild imported helper modules,
  then `lake env lean` on a hidden sibling copy of the staged source); workflow hooks unchanged (their Rocq-oriented
  classifiers are Phase 5: e.g. `has_unfinished_proof` and the final-theorem preview do not yet understand Lean).
- Tool descriptions (`lean-session.txt`, `lean-query.txt`, `lean-check.txt`, `checkpoint.txt`) rewritten for Lean.
- Tests on the PC (built package): lean-tools.integration 2, lean-session 8, lean-gate 14, lean-region 6,
  lean-term 5 = **35/35 pass**.

### Phase 5 — rest of the app (in progress, PC)

- 5a (commit 9eb24a16): source model, premise audit, review/task/projection/ledger ported; session/tool fixtures in Lean.
  `LeanProject` reads diagnostics with `lake env lean --json` (info messages carry positions, so `#print axioms`
  output is parsed from messages). proof-review 39/39.
- 5b (known-problem fixes, this commit):
  - K2/D9: `proof_plan` action `amend` (`amendment: {node, depends_on, inserts_before, addresses_escalation,
    consumer_composition_certificate?}`); the bridge node is inserted before the escalated region's plan node, the
    consumer gets the dependency and edge; only the new node is premise-audited. `accepted_amendments` ≤ 3
    (`MAX_PLAN_AMENDMENTS`), rejections free, whole-plan resubmissions after acceptance are locked (V13).
  - K3: both controller stops (`stalled_wide_fallback` family and `materialization_livelock`) carry
    `metadata.controller_stop = {reason, required_action, admit_id}`; a missing bridge against a locked plan names an
    amendment.
  - K4: `<scheduler-status>` (V12). K8: per-region escalation history keyed by region fingerprint; 3 same-type
    escalations without a change block dispatch and unlock an amendment.
  - K7: plan-owned `kind`/`layer` (V14); region target vs plan `normal_form` and K6 root goal decided by elaboration
    (V15); `normal_form` that is prose or truncated is a plan-review hard error (`normal_form_not_lean`); a real
    root-goal mismatch is a mechanical (free) error.
  - S14: before a prover run ends, the current source must have been compiled by `checkpoint`/`lean_check`; otherwise
    one `<final-validation-required>` reminder per source revision.
  - prompt.ts gap-revision §1 wording (R2 closure, `sorry`, Lean proof file, Prosa/Mathlib).
  - Tests (PC): proof-review 39/39; proof-workflow + prompt + task 139/139.
- Full-suite runs on the PC died in the 24 GB cap (V16, fixed). First complete capped PC run of the ported tree:
  **1528 pass, 20 skip, 4 fail** (baseline 1501/9/21); 3 failures are the baseline's oauth-browser timeouts, the
  4th was a fixture leftover (fixed). New tests: `known-problem-fixes.test.ts` (K4, K5, K8, S14, S26),
  `lean-statement-check.test.ts` (K6, K7); with proof-review, proof-workflow, prompt, task, bash: all pass on the PC.
- 5d (LSP, S25, K10):
  - `lsp/server.ts`: `LeanLsp` (`lake serve` in the Lake root, `.lean`; `OPENCODE_LAKE` override) replaces rocq-lsp;
    `language.ts` maps `.lean`. `lsp/client.ts`: `$/lean/fileProgress` state/event (`lsp.client.lean.file-progress`)
    replaces the Rocq server-status/progress/execution/goal machinery; `lsp/index.ts` drops `rocqGoals`,
    `rocqDocument`, `rocqSaveVo`, Petanque and their schemas (D3), status reports Lean progress.
  - S25: the client records the sha256 of every document version it sends and of the version each diagnostics set
    belongs to (`LSP.diagnosticsSourceHash`); `ProofContext.snapshot` drops diagnostics for another revision and says
    "diagnostics pending for revision …". Snapshot goals come from the session's `lean_session` state (D3).
  - `lsp` tool: `proofGoals` removed (D3, D12/K11); description points to `lean_session`. TUI sidebar/status show
    Lean processing state; `run.ts` detects Lean benchmark prompts.
  - K10: a proof agent whose model has no `limit.context` fails at the turn start with a clear message (the runner
    check is Phase 8).
  - Tests (PC): new `lean-lsp.integration.test.ts` (real `lake serve`: diagnostics + S25 hash), LSP/projection/
    compaction/known-problem 40/40, prompt 18/18.

