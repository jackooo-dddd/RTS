# `analysis/facts/busy_interval/quiet_time.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `zero_is_quiet_time` | Lemma | `Prosa.Analysis.Facts.BusyInterval.QuietTime.zero_is_quiet_time` | `zero_is_quiet_time_correspondence` | [view](3_printed_declarations/zero_is_quiet_time.md) |
| `no_carry_in_implies_quiet_time` | Lemma | `Prosa.Analysis.Facts.BusyInterval.QuietTime.no_carry_in_implies_quiet_time` | `no_carry_in_implies_quiet_time_correspondence` | [view](3_printed_declarations/no_carry_in_implies_quiet_time.md) |
| `busy_interval_prefix_no_quiet_time` | Fact | `Prosa.Analysis.Facts.BusyInterval.QuietTime.busy_interval_prefix_no_quiet_time` | `busy_interval_prefix_no_quiet_time_correspondence` | [view](3_printed_declarations/busy_interval_prefix_no_quiet_time.md) |
| `busy_interval_no_quiet_time` | Fact | `Prosa.Analysis.Facts.BusyInterval.QuietTime.busy_interval_no_quiet_time` | `busy_interval_no_quiet_time_correspondence` | [view](3_printed_declarations/busy_interval_no_quiet_time.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsQuietTimeCorrespondence`](4_correspondence/FactsQuietTimeCorrespondence.v) | Statement correspondences for `analysis/facts/busy_interval/quiet_time.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
