# `implementation/definitions/ideal_uni_scheduler.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `prev_job_nonpreemptive` | Definition | `Prosa.Implementation.Definitions.IdealUniScheduler.prev_job_nonpreemptive` | `prev_job_nonpreemptive_correspondence` | [view](3_printed_declarations/prev_job_nonpreemptive.md) |
| `allocation_at` | Definition | `Prosa.Implementation.Definitions.IdealUniScheduler.allocation_at` | `allocation_at_correspondence` | [view](3_printed_declarations/allocation_at.md) |
| `pmc_uni_schedule` | Definition | `Prosa.Implementation.Definitions.IdealUniScheduler.pmc_uni_schedule` | `pmc_uni_schedule_correspondence` | [view](3_printed_declarations/pmc_uni_schedule.md) |
| `choose_highest_prio_job` | Definition | `Prosa.Implementation.Definitions.IdealUniScheduler.choose_highest_prio_job` | `choose_highest_prio_job_correspondence` | [view](3_printed_declarations/choose_highest_prio_job.md) |
| `uni_schedule` | Definition | `Prosa.Implementation.Definitions.IdealUniScheduler.uni_schedule` | `uni_schedule_correspondence` | [view](3_printed_declarations/uni_schedule.md) |

## Certificates

None: every certificate module this file uses is shared.

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
