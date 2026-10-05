# `implementation/facts/generic_schedule.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `schedule_up_to_def` | Lemma | `Prosa.Implementation.Facts.GenericSchedule.schedule_up_to_def` | `schedule_up_to_def_correspondence` | [view](3_printed_declarations/schedule_up_to_def.md) |
| `schedule_up_to_unfold` | Lemma | `Prosa.Implementation.Facts.GenericSchedule.schedule_up_to_unfold` | `schedule_up_to_unfold_correspondence` | [view](3_printed_declarations/schedule_up_to_unfold.md) |
| `schedule_up_to_widen` | Lemma | `Prosa.Implementation.Facts.GenericSchedule.schedule_up_to_widen` | `schedule_up_to_widen_correspondence` | [view](3_printed_declarations/schedule_up_to_widen.md) |
| `schedule_up_to_empty` | Lemma | `Prosa.Implementation.Facts.GenericSchedule.schedule_up_to_empty` | `schedule_up_to_empty_correspondence` | [view](3_printed_declarations/schedule_up_to_empty.md) |
| `schedule_up_to_prefix_inclusion` | Lemma | `Prosa.Implementation.Facts.GenericSchedule.schedule_up_to_prefix_inclusion` | `schedule_up_to_prefix_inclusion_correspondence` | [view](3_printed_declarations/schedule_up_to_prefix_inclusion.md) |
| `schedule_up_to_identical_prefix` | Corollary | `Prosa.Implementation.Facts.GenericSchedule.schedule_up_to_identical_prefix` | `schedule_up_to_identical_prefix_correspondence` | [view](3_printed_declarations/schedule_up_to_identical_prefix.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsGenericScheduleCorrespondence`](4_correspondence/FactsGenericScheduleCorrespondence.v) | Statement correspondences for `implementation/facts/generic_schedule.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
