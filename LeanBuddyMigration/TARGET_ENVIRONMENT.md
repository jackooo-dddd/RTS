# What the Lean version will run on: agent, Lean Prosa, Lean environment

Everything the migration produces is used to prove the Lean case studies. This page names the exact pieces.
Mac paths are relative to `TranslationProof/`; the runs happen on the CityU PC (WSL, `ssh cityu-wsl`), paths
under `~/research/RTS/`.

## 1. The agent (to be built)

| Item | Value |
|---|---|
| Source to translate | [`prosabuddy-rocq/`](prosabuddy-rocq/BASELINE.md) — pure ProsaBuddy upstream commit `8e1de8c` (Rocq). |
| How to translate it | [`migration-suggestions/`](migration-suggestions/DECISIONS.md) — decisions, per-file notes, gap revisions, known-problem fixes ([README](README.md) gives the order). |
| Lean version (planned location) | `LeanBuddyMigration/leanbuddy/` — the translated app, same layout as `prosabuddy-rocq/` (`packages/opencode/…`, `.opencode/skill/`, `scripts/`). Copy to the PC as `~/research/RTS/leanbuddy/` for runs. |
| Runtime | Bun 1.3.10 (PC: `~/research/RTS/replicate-prosa-buddy/.tools/bin/bun`); dependencies as in `prosabuddy-rocq/bun.lock` (install with `bun install`; the reference tree has no `node_modules`). |
| Interactive backend | Pantograph **0.3.19** (commit `92d4818`, 2026-08-29), the release that moved to `leanprover/lean4:v4.33.1`. It has no git tag (tags stop at `v0.3.17`) and is on branch `dev`, so check out the full commit `92d4818a4b343d7be293731e03359a19e8082626`; built with `lake build` in its own repository and started from the run copy with `lake env` so it loads this package's build ([BACKEND_DECISION](migration-suggestions/BACKEND_DECISION.md), *Implementation answers*). **Not installed yet** on either machine. |
| Model | `gpt-6-luna`, reasoning effort `xhigh` (the current replication setting), through CLIProxyAPI on the PC at `http://127.0.0.1:8317/v1` (config `~/research/RTS/replicate-prosa-buddy/.tools/cliproxyapi/config.yaml`, kept alive by `~/research/setup/cpa_keepalive.sh`; upstream via the PC's Clash at `127.0.0.1:7890`). The provider entry must declare `limit.context` (KNOWN_PROBLEMS K10). |
| Runner | Ported last (gap-revisions §5); until then the Rocq replication runner in `replicate-prosa-buddy/scripts/` shows the expected behaviour. |

## 2. The translated Lean Prosa and the case studies

Package [`Deliverables/lean-prosa-v06/`](../Deliverables/lean-prosa-v06/README.md) (PC: `~/research/RTS/Deliverables/lean-prosa-v06/`):

| Part | Content |
|---|---|
| `Prosa/` | Lean Prosa: all 357 files of Prosa v0.6 + all 190 files of classic Prosa (`Prosa/Classic/`). |
| `CaseStudies/<G>/<F>/` | The 24 case studies: `Statement.lean` (read-only definitions and `<thm>_statement : Prop`), `Solution.lean` (`theorem solution : <thm>_statement := by sorry`, the agent's target), `proof.tex` (paper proof hint; 22 of 24). |
| `benchmark/` | `tasks.json` (24 tasks: folder, modules, names, hint file), `check.py` (the success check = DECISIONS D4), `frozen_sha256.json`, [README](../Deliverables/lean-prosa-v06/benchmark/README.md) with the rules. |
| `benchmark/prosa-theorems/` | Second benchmark: ProsaBuddy's 130 Prosa theorems (65 train / 65 test, levels 1–7), `prepare.py`, `check.py`, `tasks.json`. |
| Reference solutions | `Deliverables/lean-prosa-v06-reference-solutions/` — **never staged for the agent**. |

**Warning (PC):** the PC copy `~/research/RTS/Deliverables/lean-prosa-v06/` contains an extra `Solutions/` folder with
22 reference-solution files that the Mac copy does not have. A staging step must copy the package **without**
`Solutions/` (or stage from a clean copy); otherwise the agent can read the answers.

Related, not used for runs: `Prosa-Shunqi/` (the development workspace the package was built from) and
`RTS_Papers/` (original papers, Rocq case studies and `proof.tex`).

## 3. The Lean environment

| Item | Value |
|---|---|
| Toolchain | `leanprover/lean4:v4.33.1` (package `lean-toolchain`); installed on the PC (`~/.elan`, default `v4.33.1`) and on the Mac (`~/.elan`). |
| Dependencies | pinned in `lake-manifest.json`: Mathlib `0df444a360ea…`, plausible, LeanSearchClient, importGraph, proofwidgets, aesop. Never run `lake update`. |
| Build | **Not built yet** (no `.lake/` in either copy). Once, in a clean master copy on the PC: `lake exe cache get` then `lake build`. Every run stages its own copy with a writable build directory (see *Run staging* below). |
| Per-step check | `lake env lean <file>` on the staged `Solution.lean` (`lean_check`). |
| Final verification | `lake build <solution module>` + `python3 benchmark/check.py <task-id>` (D4). |
| LSP | Lean's language server from the same toolchain (`lake serve`); file-level diagnostics and read-only lookups (D3). |

### Run staging (DECISIONS D14)

`check.py` and the agent's own `lake build` write into `.lake`, so the build directory cannot be read-only:

| Path in the run copy | Source | Access |
|---|---|---|
| `.lake/packages/` | symlink to the master copy's `.lake/packages` (Mathlib, aesop, …) | read-only, never rebuilt |
| `.lake/build/` | writable copy of the master copy's `.lake/build` (`cp -a`; Prosa and statement `.olean`s) | `lake build <solution module>` writes the solution's and helper modules' `.olean`/`.ilean`/`.trace` here |
| `.lake/benchmark/` | created by `check.py` step 4 (the fresh `benchmark_check` file) | writable |
| sources (`Prosa/`, `Statement.lean`, `proof.tex`, `benchmark/`, package config) | copied from the clean package (never the PC's `Solutions/`) | the edit/write tools deny them; `check.py` step 1 checks their sha256 |

The edit/write tools also deny `.lake/**`. The final check never runs in the agent's workspace: the runner seeds a
fresh verification copy the same way, copies in only the agent's `CaseStudies/` files (the solution and its helper
modules), and runs `python3 benchmark/check.py <task-id> --json` there. A changed `.olean` or trace file in the
workspace therefore cannot affect the verdict. Mathlib is linked, not copied; the size of `.lake/build` (the
per-run copy cost) is known only after the first build.

## 4. Baselines to compare against

The Rocq replication of ProsaBuddy on the same 24 case studies (results, failure analysis, issue codes S1–S32):
PC `~/research/RTS/replicate-prosa-buddy/results/` (`fleet_20261008/PROSABUDDY_ISSUES.md`,
`fleet_20261009_xhigh/PROSABUDDY_ISSUES.md`), Mac `replicate-prosa-buddy/`.
