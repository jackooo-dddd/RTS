# §5 Benchmark runner — revision set

> **When to do this: last.** Port the runner only after the app translation (§1–§4, §6) is finished and its tool
> names, final gate and stop records exist; the revision files here are the specification for that step.
> **Fixed now, because the app depends on them** (the app must be built to these interfaces):
> 1. the task layout: the target is `CaseStudies/<G>/<F>/Solution.lean`, `Statement.lean` and `proof.tex` are read-only (file binding in §1 item 1);
> 2. one success definition shared by runner and agent: the D4 gate / `benchmark/check.py` (§4);
> 3. the structured `controller_stop` record the app writes when a guard ends a turn, so the runner can apply D5 (§1 item 8);
> 4. the workspace permissions the app expects: `lsp` allowed (read-only), `lake env lean` / `lake build` allowed in bash (D3), a writable `.lake/build` per run and the final check in a fresh verification copy (D14).

The runner is the Python harness around ProsaBuddy: it stages one task's workspace, starts `opencode run` with the
task prompt, retries, and decides success. In Lean it runs on the translated package
[`Deliverables/lean-prosa-v06`](../../../../Deliverables/lean-prosa-v06/README.md) (24 case studies,
`benchmark/tasks.json`; and the 130-theorem benchmark in `benchmark/prosa-theorems/`).

**Files used by the replication** (ported):

| File | Role | Revision |
|---|---|---|
| `run_casestudy_opencode_minprosa.py` (4,281 lines) | core runner: staging, attempts, retries, success check | [run_casestudy_opencode_minprosa.py-revision.md](run_casestudy_opencode_minprosa.py-revision.md) |
| `run_casestudy_our_minprosa.py` (766 lines) | ProsaBuddy-mode wrapper: segmented workflow, first-attempt/continuation prompts, skills | [run_casestudy_our_minprosa.py-revision.md](run_casestudy_our_minprosa.py-revision.md) |
| `opencode_our_prompt.md` (100 lines) | task prompt template used by the wrapper | [opencode_our_prompt.md-revision.md](opencode_our_prompt.md-revision.md) |
| `opencode_runner_config.py` + `opencode_runner_config.env` | environment defaults, nohup/lock management | [opencode_runner_config-revision.md](opencode_runner_config-revision.md) |
| `opencode_our_local.sh` | launches the OpenCode app with `bun` | [opencode_our_local.sh-revision.md](opencode_our_local.sh-revision.md) |

**Not translated** (unused in the replication, DECISIONS D6): the 15 model/case-specific launch scripts
(`run_deepseek_*.sh`, `run_ecrts_*.sh`, `run_gpt56luna_*.sh`, `run_book_*.sh`, `run_scheduled_*.sh`,
`launch_lemma3_retries20.sh`, `run_casestudy_*_minprosa*.sh`, `run_casestudy_*_easy.sh`), `opencode_runner_config.sh`
(only sourced by those launchers), `run_casestudy_decompose.py`, `opencode_prompt.md` (core-mode template; the wrapper
uses `opencode_our_prompt.md`), `opencode_trace_local.sh`, `import_historical_theorem6_trace.py`,
`crontab_prosabuddy_20260813_0400.txt`, `archived/`. Their unit tests (`test_run_casestudy_decompose.py`) go too;
`test_opencode_runner_config.py` and `test_run_casestudy_continuation_prompt.py` are handled in gap-revisions §7.

Replication setup to reproduce in Lean (from our `scripts/opencode_runner_config.env`): `OPENCODE_ENABLE_SKILL=1`,
`OPENCODE_WITH_PAPER=1`, `OPENCODE_FULL_PROSA=1`, `OPENCODE_MAX_TOTAL_TOKENS=80000000`, `OPENCODE_MAX_RETRIES=8`,
segmented proof workflow on, **direct-probe mode off** (`OPENCODE_OUR_DIRECT_PROSA_PROBE=0`). Note: the team's
default (`opencode_runner_config.py` L76-L79) turns the direct probe **on** (a `whole-lemma` attempt of up to 50 steps
/ 30 min before the segmented workflow). Port the probe (R7) but keep it off by default until it is evaluated.
