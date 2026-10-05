# `analysis/facts/busy_interval/pi_bound.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `priority_inversion_is_bounded` | Lemma | `Prosa.Analysis.Facts.BusyInterval.PiBound.priority_inversion_is_bounded` | `priority_inversion_is_bounded_correspondence` | [view](3_printed_declarations/priority_inversion_is_bounded.md) |

## Certificates

| Module | Role |
|---|---|
| [`PiBoundCorrespondence`](4_correspondence/PiBoundCorrespondence.v) | Statement correspondence for `analysis/facts/busy_interval/pi_bound.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
