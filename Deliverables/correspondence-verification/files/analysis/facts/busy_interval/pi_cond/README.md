# `analysis/facts/busy_interval/pi_cond.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `cum_task_pi_eq` | Lemma | `Prosa.Analysis.Facts.BusyInterval.PiCond.cum_task_pi_eq` | `cum_task_pi_eq_correspondence` | [view](3_printed_declarations/cum_task_pi_eq.md) |

## Certificates

| Module | Role |
|---|---|
| [`PiCondCorrespondence`](4_correspondence/PiCondCorrespondence.v) | Statement correspondence for `analysis/facts/busy_interval/pi_cond.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
