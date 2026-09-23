# Imported Lean declarations: Rocq inspection

Inspection time: 2026-09-23 22:25 (Asia/Hong_Kong). Rocq version:
`9.3+rc1` (`rocq93rc1` opam switch).

The source artifact is the latest successful *published Time-target validation artifact*: the accepted `FOUNDATION_SLICE_1` validation of `behavior/time.v` (`Validation/planning/v06_pipeline/foundation_slice_1_status.json`: `PASS`, `instant` and `duration` accepted). A newer successful validation of an unrelated module would not provide the requested `Prosa_Behavior_Time_instant`. The actual Lean export is `Validation/imported/foundation_slice_1/Time.out`, SHA-256 `8b2354769dc908175b0386f4fb1b2113be48db89164e384fe34b5539264e115a`. The inspection source is [`ImportedLeanInspection.v`](ImportedLeanInspection.v), containing exactly the requested `Set Printing All` and four `Print` commands, plus the two required imports.

The previously published `Validation/imported/foundation_slice_1/ImportedTime.vo` could **not** be loaded against the current importer foundation: Rocq reported `Compiled library FoundationImported.ImportedTime ... makes inconsistent assumptions over library LeanImport.Lean`. To avoid inspecting a stale `.vo`, I re-imported the **same** `Time.out` into isolated `Validation/.work/inspection_time/`; Rocq import succeeded. The resulting `ImportedTime.vo` SHA-256 is `f69163824deb0ca80baad1c60c09b29ff1f8f6e10abbed39dd24b6544edbe72e`. The current importer `Lean.vo` SHA-256 is `0ec01795b0a3d6646fb72824262eb7888677ac3ee4cbfc665f6a68309c54fd70`. This inspection does not change the accepted certificate or production Lean source; the original published `.vo` remains untouched.

Command run from `Reports/inspection/`:

```sh
opam exec --switch=rocq93rc1 -- rocq c \
  -Q ../../Validation/.work/tooling/rocq-lean-import/src LeanImport \
  -I ../../Validation/.work/tooling/rocq-lean-import/src \
  -Q ../../Validation/.work/inspection_time FoundationImported \
  ImportedLeanInspection.v
```

Exit status: `0`. The complete raw stdout is also saved at `Validation/logs/inspection/imported_lean_inspection.stdout` (SHA-256 `88d84c51aa0973f2bc5961ef3c60c61953e77b90c9a8962ac250172b4c884340`). It is reproduced verbatim below; the first three `Print` commands each print the inductive declaration containing the queried object.

```text
Inductive Nat@{} : Set :=  Nat_zero : Nat | Nat_succ : forall _ : Nat, Nat.

Arguments Nat_succ _%_Nat_scope
Inductive Nat@{} : Set :=  Nat_zero : Nat | Nat_succ : forall _ : Nat, Nat.

Arguments Nat_succ _%_Nat_scope
Inductive Nat@{} : Set :=  Nat_zero : Nat | Nat_succ : forall _ : Nat, Nat.

Arguments Nat_succ _%_Nat_scope
Prosa_Behavior_Time_instant@{} = Nat
     : Type
```

Interpretation:

| Command | Exact object shown in this Rocq environment |
| --- | --- |
| `Print Nat.` | Imported Lean `Nat` is an inductive in `Set` with constructors `Nat_zero : Nat` and `Nat_succ : Nat → Nat`; it is distinct from Rocq's built-in `nat`. |
| `Print Nat_zero.` | Rocq prints its parent inductive; the constructor has type `Nat`. |
| `Print Nat_succ.` | Rocq prints its parent inductive; the constructor has type `forall _ : Nat, Nat`. |
| `Print Prosa_Behavior_Time_instant.` | Actual imported compiled Lean alias has body `Nat` and type `Type`. |

This is inspection of the imported compiled artifact, not a new semantic certificate or revalidation of the accepted one.
