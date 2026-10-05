# `implementation/facts/ideal_uni/prio_aware.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `uni_schedule_work_conserving` | Corollary | `Prosa.Implementation.Facts.IdealUni.PrioAware.uni_schedule_work_conserving` | `uni_schedule_work_conserving_correspondence` | [view](3_printed_declarations/uni_schedule_work_conserving.md) |
| `uni_schedule_valid` | Corollary | `Prosa.Implementation.Facts.IdealUni.PrioAware.uni_schedule_valid` | `uni_schedule_valid_correspondence` | [view](3_printed_declarations/uni_schedule_valid.md) |
| `schedule_respects_preemption_model` | Corollary | `Prosa.Implementation.Facts.IdealUni.PrioAware.schedule_respects_preemption_model` | `schedule_respects_preemption_model_correspondence` | [view](3_printed_declarations/schedule_respects_preemption_model.md) |
| `scheduled_job_is_supremum` | Lemma | `Prosa.Implementation.Facts.IdealUni.PrioAware.scheduled_job_is_supremum` | `scheduled_job_is_supremum_correspondence` | [view](3_printed_declarations/scheduled_job_is_supremum.md) |
| `schedule_respects_policy` | Theorem | `Prosa.Implementation.Facts.IdealUni.PrioAware.schedule_respects_policy` | `schedule_respects_policy_correspondence` | [view](3_printed_declarations/schedule_respects_policy.md) |

## Certificates

| Module | Role |
|---|---|
| [`PreemptionAwareHelpers`](4_correspondence/PreemptionAwareHelpers.v) | Helper certificates of `implementation/facts/ideal_uni/preemption_aware.v` (its accepted PreemptionAwareCorrespondence up to, and excluding, its statement correspondences, whose target statements are … |
| [`PrioAwareCorrespondence`](4_correspondence/PrioAwareCorrespondence.v) | Statement correspondences for `implementation/facts/ideal_uni/prio_aware.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
