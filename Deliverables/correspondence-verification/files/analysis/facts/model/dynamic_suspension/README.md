# `analysis/facts/model/dynamic_suspension.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `job_suspension_bounded` | Lemma | `Prosa.Analysis.Facts.Model.DynamicSuspension.job_suspension_bounded` | `job_suspension_bounded_correspondence` | [view](3_printed_declarations/job_suspension_bounded.md) |
| `suspension_of_task_bounded` | Lemma | `Prosa.Analysis.Facts.Model.DynamicSuspension.suspension_of_task_bounded` | `suspension_of_task_bounded_correspondence` | [view](3_printed_declarations/suspension_of_task_bounded.md) |

## Certificates

| Module | Role |
|---|---|
| [`DsPStateCover`](4_correspondence/DsPStateCover.v) | Port of the accepted certificates/results_rta_arm_edf_fully_preemptive/RsPStateCover.v (two-way processor-state cover) to this export and to the JitterSvc Service relation modules (whose … |
| [`FactsDynamicSuspensionCorrespondence`](4_correspondence/FactsDynamicSuspensionCorrespondence.v) | Statement certificates for `analysis/facts/model/dynamic_suspension.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
