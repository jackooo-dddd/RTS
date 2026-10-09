# Revision: `scripts/validate_classified_ast.py` (1,021 lines) — replaced, not ported

**File**: [`scripts/validate_classified_ast.py`](../../../prosabuddy-rocq/scripts/validate_classified_ast.py). **Change**: delete after the
gate exists. **Follows**: DECISIONS D4.

Rule-by-rule mapping, so nothing is silently lost:

| Rocq rule (reason code) | Purpose | Lean gate equivalent |
|---|---|---|
| Target declaration unchanged | statement preserved | stage `final` check 4 (fresh `theorem gate_check : <statement> := <solution>`) + frozen statement module (check 1). |
| `EXTERIOR_AST_CHANGED` ([#L784](../../../prosabuddy-rocq/scripts/validate_classified_ast.py#L784)) | nothing outside the proof changed | frozen files (check 1); in the solution file, added helper declarations and `import`s of package modules are allowed (benchmark rules, K1); submission stage: `REGION_OUTSIDE_EDIT`. |
| `PROOF_SYNTERP_FORBIDDEN` ([#L556](../../../prosabuddy-rocq/scripts/validate_classified_ast.py#L556)) | no vernacular commands inside a proof | not needed: Lean has no in-proof `Require`; meta-programming escapes are caught by the token scan (`run_cmd`, `run_elab`, `elab`, `#eval`, …). |
| `Admitted`/`admit`/`Axiom`/`Parameter` bans | no unproved assumptions | token scan (`sorry`, `admit`, `axiom`) + `#print axioms` (check 5). |
| Allowed proof-step vernacular list, `Opaque`/`Transparent`, plugins | no environment tampering | token scan (`set_option debug.`, `unsafe`, `implemented_by`, `@[extern`, `initialize`). |
| Trusted `Require` roots (`mathcomp`, `prosa`) | which libraries may be loaded | any module of the package (`Prosa.*`, `Mathlib.*`, statement and helper modules) may be imported. |

If a later review finds a check that this table drops, add it to the gate as a new reason code rather than reviving
an AST pipeline.
