# Prosa v0.6 Translation Workspace Setup Report

**Completed:** 2026-09-20 20:18:47 HKT  
**Scope:** workspace scaffold only; no Prosa declaration translated

## Workspace created

The new isolated workspace is rooted at `Prosa-Shunqi/` and contains:

```text
Prosa-Shunqi/
├── Prosa/
│   ├── Behavior/
│   ├── Util/
│   ├── Model/
│   ├── Analysis/
│   ├── Results/
│   └── Implementation/
├── Validation/
│   ├── planning/{v06_dependency,v06_mapping,v06_pipeline}/
│   ├── scripts/
│   ├── certificates/
│   ├── fixtures/
│   ├── imported/
│   └── logs/
├── Reports/
├── lakefile.lean
├── lake-manifest.json
├── lean-toolchain
└── README.md
```

Empty production and validation directories use `.gitkeep`. `.lake/` and Lean
build outputs are excluded by the workspace `.gitignore`.

## Authority and isolation

- Authoritative source: Prosa v0.6 commit
  `414e66760333eaa4ef78c685bcf53291c527a548`.
- Historical source reference: Prosa v0.4 commit
  `ee05f255e29676ad79e07b5d6cc59dc66cd7fcb7`.
- Historical Lean reference: `../Prosa-fei/Prosa/`, read-only by default.
- Production coverage is defined exclusively by accepted Lean declarations
  under `Prosa-Shunqi/Prosa/`.

`Prosa-Shunqi/Prosa/` contains six `.gitkeep` files and **zero `.lean` files**.
No historical translation file, prototype, fixture, report, or certificate was
copied into production.

The historical production tree remains unchanged at Git tree object
`7426e874bd049e6f007b2695ef13f7209a0a1f8f`; `git status --
Prosa-fei/Prosa` is empty.

## Planning snapshots

The accepted preparation artifacts were copied without moving or deleting the
historical copies:

- `v06_dependency/`: 33 files after excluding the untracked Python cache;
- `v06_mapping/`: 17 files;
- recursive snapshot comparison against the source directories: identical.

The copied evidence intentionally retains historical absolute paths or
explicit `Prosa-fei` references. Seven copied files contain such references:

```text
v06_dependency/generate_v06_inventory.py
v06_dependency/logs/elaborated_type_probe.stderr
v06_dependency/logs/reproduction_manifest.txt
v06_dependency/reproduce.sh
v06_dependency/scope_manifest.json
v06_dependency/v06_dependency_report.md
v06_mapping/reproduce.sh
```

These paths were recorded, not rewritten. Copied reproduction scripts are
snapshot evidence; a future pipeline stage must create a new
`Prosa-Shunqi`-specific entry point rather than falsifying historical records.

## Lean and Mathlib

- Lean toolchain: `leanprover/lean4:v4.33.1`.
- Observed Lean/Lake: Lake `5.0.0-src+819816b`, Lean `4.33.1`.
- Mathlib input and resolved revision:
  `0df444a360eaa60ab8c11dca51a86af692955474`.
- Package: `prosa_v06_translation`.
- Library root: `Prosa` with `autoImplicit := false`.

`lake update` created `lake-manifest.json` and checked out the exact approved
Mathlib revision. No upgrade was performed.

## Smoke checks

| Check | Result |
|---|---|
| `lake update` with pinned revision | PASS |
| empty `Prosa` library `lake build` | PASS (`Build completed successfully`) |
| validation-only `WorkspaceSmoke.lean` via `lake env lean` | PASS |
| production `.lean` file count | PASS: 0 |
| dependency planning snapshot present | PASS |
| mapping planning snapshot present | PASS |
| historical production status | PASS: unchanged |
| `git diff --check` | PASS |

The smoke fixture is stored under `Validation/fixtures/`; it is not a Prosa
translation declaration and is excluded from production coverage. Raw smoke
logs are under `Validation/logs/`.

```text
V06_WORKSPACE_READY = YES
```
