# `analysis/facts/preemption/rtc_threshold/limited.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `number_of_preemption_points_in_task_at_least_two` | Remark | `Prosa.Analysis.Facts.Preemption.RtcThreshold.Limited.number_of_preemption_points_in_task_at_least_two` | `number_of_preemption_points_in_task_at_least_two_correspondence` | [view](3_printed_declarations/number_of_preemption_points_in_task_at_least_two.md) |
| `limited_valid_task_run_to_completion_threshold` | Lemma | `Prosa.Analysis.Facts.Preemption.RtcThreshold.Limited.limited_valid_task_run_to_completion_threshold` | `limited_valid_task_run_to_completion_threshold_correspondence` | [view](3_printed_declarations/limited_valid_task_run_to_completion_threshold.md) |
| `last_segment_eq_cost_minus_rtct` | Lemma | `Prosa.Analysis.Facts.Preemption.RtcThreshold.Limited.last_segment_eq_cost_minus_rtct` | `last_segment_eq_cost_minus_rtct_correspondence` | [view](3_printed_declarations/last_segment_eq_cost_minus_rtct.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsRtcLimitedCorrespondence`](4_correspondence/FactsRtcLimitedCorrespondence.v) | Statement correspondences for `analysis/facts/preemption/rtc_threshold/limited.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
