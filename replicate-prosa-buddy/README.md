# ProsaBuddy replication (Rocq, single theorem, gpt-6-luna)

Replicates one ProsaBuddy case-study experiment, `2005-ECRTS-Lemma3`, with the original ProsaBuddy
agents, prompts, skills, tools and experiment runner. The differences are the model (`gpt-6-luna` through a
local CLIProxyAPI) and the Rocq/Prosa environment of this machine (opam switch `prosa-0.6`).

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
| `scripts/run_lemma3_gpt6luna.sh` | Launcher for this replication (mirrors the original launcher) | new |
| `prosa_v06/` | Prosa v0.6 (`analysis behavior implementation model results util`) + ProsaBuddy's `classic`, `.v` sources compiled here with Rocq 9.0.1 | `prosabuddy/prosaworkspace/` (symlinks resolved) |
| `datasets_v06/casestudy_v06/2005-ECRTS-Lemma3/` | Case-study input: `Lemma3.v` + the paper PDF | `../RTS_Papers/2005-ECRTS-Lemma3/` |
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
| coq-lsp / `fcc` | unknown | not installed: `petanque` tool returns an error, runtime AST audit reports `disabled` (default `auto` mode) | not installed in the switch; the runner's own integrity + `coqc` check still applies |
| `setsid` | util-linux `setsid` (Linux) | `.tools/bin/setsid`, a 20-line C shim (`.tools/src/setsid.c`): `setsid()` then `exec`, same pid/process-group semantics | `tool/coq-project.ts` runs every `coqc`/`coqtop`/`coq_session` call as `setsid <cmd>`; macOS has no `setsid`. The first launch failed every Coq call for this reason and was stopped (kept in `results/aborted/`) |
| Claude Code integration | n/a | `OPENCODE_DISABLE_CLAUDE_CODE=1` | keeps `~/.claude/skills` on this Mac out of the agent's skill list |
| `proof.tex` | used when the case directory has one | none for this case in `RTS_Papers` | not available |

## Run

Requires CLIProxyAPI running (`brew services info cliproxyapi`) and `prosa_v06` compiled.

```bash
scripts/run_lemma3_gpt6luna.sh            # 2005-ECRTS-Lemma3
```

Rebuild Prosa: `cd prosa_v06 && eval $(opam env --switch=prosa-0.6 --set-switch) && make -f Makefile.build -j8`
(regenerate `Makefile.build` from `_CoqProject.build` with `rocq makefile -f _CoqProject.build -o Makefile.build`).

## Results

(filled in after the run)
