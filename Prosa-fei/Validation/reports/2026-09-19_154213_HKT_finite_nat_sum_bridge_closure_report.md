# Finite Nat Sum Bridge Closure Report

**Experiment 6 start:** 2026-09-19 15:42:13 HKT  
**Frozen repository commit:** `e3895e2055ec17a99eb3cf51542732dd961b7b10`  
**Pinned official Prosa source:** Prosa 0.6, commit `414e66760333eaa4ef78c685bcf53291c527a548`  
**Rocq:** 9.3+rc1  
**Scope:** close `FiniteNatSumValueBridge`; no changes under `Prosa/`.

## Progress log

### 2026-09-19 15:42:13 HKT — experiment initialized

- Confirmed the production translation remains outside the modification scope.
- Existing Experiment 5 result is `PARAMETRICALLY_CERTIFIED` because `big_nat_eq0_parametric_certificate` takes `FiniteNatSumValueBridge` as an explicit semantic premise.
- Planned proof decomposition: actual imported `Finset.Ico` enumeration → imported list/multiset representation → imported fold/sum → MathComp interval big operator.
- No Experiment 6 certificate is claimed at this timestamp.

### 2026-09-19 15:44:05 HKT — actual imported interval recursion exposed

- Added `Validation/rocq/FiniteNatSumBridge.v`; no production Lean file was changed.
- Rocq 9.3+rc1 kernel accepted definitional equations for the actual imported Lean constants `List_range'`, `Nat_add`, and Lean's imported numeral `1`.
- In particular, `List_range' start 0 step = []` and
  `List_range' start (Nat.succ len) step = start :: List_range' (start + step) len step`
  were proved by `eq_refl`, showing that the importer representation is computationally transparent enough for an inductive interval-enumeration proof.
- Reproduction command:

  ```bash
  cd Validation/rocq
  opam exec --switch=rocq93rc1 -- rocq c \
    -R "$HOME/.opam/prosa-0.6/.opam-switch/sources/rocq-prosa.0.6" prosa \
    -Q /private/tmp/rocq-lean-import-93/src LeanImport \
    -I /private/tmp/rocq-lean-import-93/src \
    -Q generated_hard HardSource \
    FiniteNatSumBridge.v
  ```
- Machine result: **PASS**. Log: `reports/logs/experiment6_finite_sum_bridge.log`.
- This closes only the imported range recursion subproblem. `FiniteNatSumValueBridge` itself is not yet closed at this timestamp.

### 2026-09-19 15:55:21 HKT — `FiniteNatSumValueBridge` closed

- Implemented a compositional value proof against the actual imported constants:
  `Finset_sum_inst3` / `Finset_Ico_inst1` → `List_range'` → imported `List.map` → imported `List.foldr` → MathComp `iota` / `bigop`.
- Added reusable lemmas for imported/source natural addition, subtraction, range enumeration, list mapping, list summation, and MathComp big-sequence folding.
- `finite_nat_sum_value_bridge_prop` proves the complete value equality in Rocq `Prop`; `finite_nat_sum_value_bridge_closed` transfers exactly that proved equality to the importer's `SProp` equality.
- Because Rocq forbids eliminating a native `Prop` equality into imported `SProp`, isolated the generic bridge `prop_sprop_trusted_eq_intro` in `Validation/rocq/PropSPropBridge.v`. This is a visible trust boundary, not a sum-specific assumption.
- Rocq 9.3+rc1 accepted `finite_nat_sum_value_bridge_closed`. It has **no validation-specific semantic premise**.
- `Print Assumptions finite_nat_sum_value_bridge_closed` reports the explicit `prop_sprop_trusted_eq_intro` boundary plus assumptions from the imported Lean foundation/artifact (including definitional UIP and imported theorem/foundation constants). Therefore the honest status is `CERTIFIED_WITH_PROP_SPROP_BRIDGE`, not axiom-free `CERTIFIED`.
- Next: compose this closed bridge into `big_nat_eq0_parametric_certificate`, audit the resulting closed theorem, and rerun the `sum = 1` mutation.

### 2026-09-19 15:56:15 HKT — `big_nat_eq0` upgraded and mutation rejected

- Added `big_nat_eq0_closed_certificate`; it supplies the proved `finite_nat_sum_value_bridge_closed` to the earlier compositional theorem certificate. There is no `Hsum` or other validation-specific premise in its type.
- Rocq kernel result: **PASS** for the closed certificate.
- `Print Assumptions big_nat_eq0_closed_certificate` contains:
  - explicit validator boundary `prop_sprop_trusted_eq_intro` and existing `prop_sprop_trusted_elim`;
  - importer/actual-artifact foundation assumptions, including the statement-only imported `Prosa_Util_Sum_big_nat_eq0`, definitional UIP notices, primitive `Int63` declarations, and imported Mathlib theorem constants;
  - **no `FiniteNatSumValueBridge` premise and no validation-specific semantic axiom**.
- Final honest status for `big_nat_eq0`: **CERTIFIED_WITH_PROP_SPROP_BRIDGE** (upgraded from `PARAMETRICALLY_CERTIFIED`).
- Updated the mutation fixture to reuse `big_nat_eq0_closed_certificate` directly, with no bridge hypothesis. Rocq accepted the enclosing `Fail Definition`, confirming that replacing `sum = 0` by `sum = 1` is rejected.
- Mutation result: **PASS**. Logs:
  - `reports/logs/experiment6_finite_sum_bridge.log`
  - `reports/logs/experiment6_big_nat_eq0_mutation.log`

### 2026-09-19 15:57:57 HKT — official reuse targets exported and imported

- Confirmed two additional declarations exist in the pinned official Prosa 0.6 `util/sum.v` and in the frozen Lean translation: `sum_of_ones` and `sum_le_summation_range`.
- Automatic source acquisition recorded official source hashes in `reports/logs/experiment6_source_fidelity.json`:
  - `sum_of_ones` source block SHA-256 `1bee82e32e536ca2e790e6a09c2785f90ebc61783eb388111d65a745139f918a`;
  - `sum_le_summation_range` source block SHA-256 `57abcd9d4768e376b9d5198b19b2af15c27577822ac9395cc64667c85c9b4c80`.
- Exported their real compiled Lean statements together with `big_nat_eq0` using the generic statement-only exporter. Artifact: `Validation/export/FiniteNatSumTargets.out`, SHA-256 `20aefd4c4cd26b73c196b6c7e74a109efa565cd3214d1938f92bd4415daa1f69`.
- `rocq-lean-import` successfully imported all three actual theorem constants under Rocq 9.3+rc1. Log reaches `Prosa.Util.Sum.sum_of_ones` at artifact line 7314 and `Prosa.Util.Sum.sum_le_summation_range` at line 7346, then reports `Done!`.
- This timestamp establishes provenance and actual-artifact availability only; semantic certificates for the two reuse targets are still pending.

### 2026-09-19 16:05:01 HKT — bridge reused by two official Prosa 0.6 theorems

- Added `FiniteNatSumReuseCertificates.v`, referencing both the automatically generated official-source module and actual constants imported from `FiniteNatSumTargets.out`.
- `sum_of_ones_statement_certificate`: Rocq kernel **PASS**. The bidirectional statement relation reuses the same finite interval sum value bridge plus Nat addition/injectivity. `Print Assumptions` shows `prop_sprop_trusted_eq_intro`, `prop_sprop_trusted_elim`, and importer/artifact assumptions; no validation-specific premise remains. Status: **CERTIFIED_WITH_PROP_SPROP_BRIDGE**.
- `sum_le_summation_range_statement_certificate`: Rocq kernel **PASS**. It reuses the finite sum bridge, Nat `<`/`≤` bridges, endpoint-addition correspondence, canonical higher-order function relation, and the explicit witness-crossing bridge. `Print Assumptions` shows `prop_sprop_trusted_exists_intro`, `prop_sprop_trusted_eq_intro`, `prop_sprop_trusted_elim`, and importer/artifact assumptions; no validation-specific premise remains. Status: **CERTIFIED_WITH_PROP_SPROP_BRIDGE**.
- Both imported statement witnesses type-check against the exact actual theorem constants `Prosa_Util_Sum_sum_of_ones` and `Prosa_Util_Sum_sum_le_summation_range`; both official source witnesses type-check against automatically extracted `Generated_util__sum` declarations.
- Reuse result: one finite-sum bridge now supports three real official Prosa 0.6 theorem targets: `big_nat_eq0`, `sum_of_ones`, and `sum_le_summation_range`.
- Machine log: `reports/logs/experiment6_finite_sum_reuse_certificates.log`.

### 2026-09-19 16:07:05 HKT — reproducible validator completed

- Added executable `Validation/scripts/validate_finite_nat_sum_bridge.sh` and ran it end to end successfully.
- The command performs official-source extraction/fidelity capture, optional real Lean re-export (`REEXPORT=1`), actual artifact import, bridge/certificate compilation, forbidden-token and unexpected-axiom checks, assumption printing, mutation compilation, and a concise status summary.
- Final machine summary:

  ```text
  FiniteNatSumValueBridge        CERTIFIED_WITH_PROP_SPROP_BRIDGE
  big_nat_eq0                    CERTIFIED_WITH_PROP_SPROP_BRIDGE
  sum_of_ones                    CERTIFIED_WITH_PROP_SPROP_BRIDGE
  sum_le_summation_range         CERTIFIED_WITH_PROP_SPROP_BRIDGE

  Validation-specific premises: none
  Mutation: sum = 0 -> sum = 1   PASS (closed certificate rejected)
  ```
- `git diff --name-only -- Prosa` produced no output: the frozen production Lean translation was not modified.
- `git diff --check`, shell syntax checks, YAML parsing, and the forbidden `Admitted` / `admit` / `sorry` scan all passed.

## Final result table

| Target | Official Prosa 0.6 source | Actual Lean artifact imported | Own correspondence | Validation-specific premise | Trust status | Mutation |
| --- | --- | --- | --- | --- | --- | --- |
| `FiniteNatSumValueBridge` | MathComp `index_iota` / `bigop` semantics | actual imported `Finset.Ico` / `Finset.sum` body | pass | none | `CERTIFIED_WITH_PROP_SPROP_BRIDGE` | n/a |
| `big_nat_eq0` | yes, auto-extracted | yes | pass, bidirectional | none | `CERTIFIED_WITH_PROP_SPROP_BRIDGE` | PASS |
| `sum_of_ones` | yes, auto-extracted | yes | pass, bidirectional | none | `CERTIFIED_WITH_PROP_SPROP_BRIDGE` | not separately needed |
| `sum_le_summation_range` | yes, auto-extracted | yes | pass, bidirectional | none | `CERTIFIED_WITH_PROP_SPROP_BRIDGE` | not separately needed |

## Trust accounting

The result is fully closed with respect to validation-specific semantic dependencies: `FiniteNatSumValueBridge` is a theorem, not a parameter. It is not called axiom-free because the following explicit generic Prop/SProp boundaries remain visible in `Print Assumptions`:

- `prop_sprop_trusted_eq_intro`: transports a proved Rocq `Logic.eq` into the importer's Lean-equality `SProp`;
- `prop_sprop_trusted_elim`: permits recovery of a Rocq proposition from its strict inhabitance;
- `prop_sprop_trusted_exists_intro`: used only where a Rocq existential witness must cross into imported Lean `Exists` (`sum_le_summation_range`).

The assumption output also includes importer/Lean foundation declarations (for example definitional UIP notices, primitive `Int63` constants, and statement-only imported Lean theorem/dependency constants). These are artifact/import boundaries, not unproved validation premises. No `Axiom` occurs outside the isolated `PropSPropBridge.v` allowlist.

## Reusable bridge decomposition

The reusable finite-sum infrastructure now consists of:

1. Rocq `nat` ↔ imported Lean `Nat`, including addition, subtraction, order, and injectivity;
2. MathComp `iota m (n-m)` ↔ imported Lean `List.range' m (n-m) 1`;
3. MathComp `seq.map` / `foldr addn 0` ↔ imported Lean `List.map` / `List.foldr Nat.add 0`;
4. definitional reduction of actual imported `Finset.Ico` and `Finset.sum` through `Finset.val`, `Multiset.map`, and `Multiset.sum`;
5. higher-order canonical function correspondence;
6. compositional reuse with equality, order, implication, conjunction, and existential relations.

Coverage in this experiment is **three downstream official theorem targets** from one closed sum bridge. This is credible reusable infrastructure for later interval-sum declarations. Scaling to 50–100 declarations will still require bridges for additional monoids, filtered sums, products, and richer index types; those are extensions of the same decomposition, not a remaining hole in the Nat interval-sum case.

## Reproduction

From `Prosa-fei/Validation`:

```bash
./scripts/validate_finite_nat_sum_bridge.sh
```

To regenerate the actual Lean export first:

```bash
REEXPORT=1 ./scripts/validate_finite_nat_sum_bridge.sh
```

The validated artifact is `export/FiniteNatSumTargets.out` (7,346 lines, 142,576 bytes), SHA-256 `20aefd4c4cd26b73c196b6c7e74a109efa565cd3214d1938f92bd4415daa1f69`.

## Conclusion

`FiniteNatSumValueBridge` is closed. `big_nat_eq0` is upgraded from `PARAMETRICALLY_CERTIFIED` to `CERTIFIED_WITH_PROP_SPROP_BRIDGE`. The same actual-artifact bridge successfully certifies two additional declarations that genuinely exist in pinned official Prosa 0.6. No translation mismatch was found in this Nat interval-sum slice, and no production Lean source was changed.

### 2026-09-19 16:09:01 HKT — clean full re-export run confirmed

- Ran `REEXPORT=1 Validation/scripts/validate_finite_nat_sum_bridge.sh` from the repository root.
- Lean compilation and generic statement-only export completed successfully for all three configured theorem names.
- The regenerated artifact has the same SHA-256 `20aefd4c4cd26b73c196b6c7e74a109efa565cd3214d1938f92bd4415daa1f69`, demonstrating deterministic reproduction in this environment.
- The regenerated artifact was then imported and every bridge, certificate, assumption audit, forbidden-token check, and mutation fixture passed in the same invocation.
- Final `git diff --check`: pass. Final production-tree diff (`git diff --name-only -- Prosa`): empty.
