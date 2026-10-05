# `model/schedule/nonpreemptive.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `nonpreemptive_schedule` | Definition | `Prosa.Model.Schedule.Nonpreemptive.nonpreemptive_schedule` | `nonpreemptive_schedule_correspondence` | [view](3_printed_declarations/nonpreemptive_schedule.md) |

## Certificates

| Module | Role |
|---|---|
| [`NonpreemptiveExactTypeGuards`](4_correspondence/NonpreemptiveExactTypeGuards.v) | Exact elaborated signatures of the official v0.6 declaration and the actual imported Lean definition. |
| [`NonpreemptiveCorrespondence`](4_correspondence/NonpreemptiveCorrespondence.v) | The twelve v0.6 Service definitions, proved compositionally from the actual imported Lean bodies and the separately audited operation relations. |
| [`NonpreemptiveScheduleCorrespondence`](4_correspondence/NonpreemptiveScheduleCorrespondence.v) | The only public v0.6 Nonpreemptive definition. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
