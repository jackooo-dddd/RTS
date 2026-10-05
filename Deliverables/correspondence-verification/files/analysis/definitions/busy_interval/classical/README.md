# `analysis/definitions/busy_interval/classical.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `quiet_time` | Definition | `Prosa.Analysis.Definitions.BusyInterval.Classical.quiet_time` | `quiet_time_correspondence` | [view](3_printed_declarations/quiet_time.md) |
| `busy_interval_prefix` | Definition | `Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix` | `busy_interval_prefix_correspondence` | [view](3_printed_declarations/busy_interval_prefix.md) |
| `busy_interval` | Definition | `Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval` | `busy_interval_correspondence` | [view](3_printed_declarations/busy_interval.md) |
| `quiet_time_dec` | Definition | `Prosa.Analysis.Definitions.BusyInterval.Classical.quiet_time_dec` | `quiet_time_dec_correspondence` | [view](3_printed_declarations/quiet_time_dec.md) |
| `quiet_time_P` | Lemma | `Prosa.Analysis.Definitions.BusyInterval.Classical.quiet_time_P` | `quiet_time_P_correspondence` | [view](3_printed_declarations/quiet_time_P.md) |

## Certificates

| Module | Role |
|---|---|
| [`BusyIntervalClassicalCorrespondence`](4_correspondence/BusyIntervalClassicalCorrespondence.v) | Certificates for `analysis/definitions/busy_interval/classical.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
