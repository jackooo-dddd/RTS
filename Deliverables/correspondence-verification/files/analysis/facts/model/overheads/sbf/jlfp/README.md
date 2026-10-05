# `analysis/facts/model/overheads/sbf/jlfp.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `jlfp_blackout_bound` | Definition | `Prosa.Analysis.Facts.Model.Overheads.Sbf.Jlfp.jlfp_blackout_bound` | `jlfp_blackout_bound_correspondence` | [view](3_printed_declarations/jlfp_blackout_bound.md) |
| `jlfp_ovh_sbf_slow` | Definition | `Prosa.Analysis.Facts.Model.Overheads.Sbf.Jlfp.jlfp_ovh_sbf_slow` | `jlfp_ovh_sbf_slow_correspondence` | [view](3_printed_declarations/jlfp_ovh_sbf_slow.md) |
| `overheads_sbf_monotone` | Lemma | `Prosa.Analysis.Facts.Model.Overheads.Sbf.Jlfp.overheads_sbf_monotone` | `overheads_sbf_monotone_correspondence` | [view](3_printed_declarations/overheads_sbf_monotone.md) |
| `jlfp_blackout_bound_monotone` | Remark | `Prosa.Analysis.Facts.Model.Overheads.Sbf.Jlfp.jlfp_blackout_bound_monotone` | `jlfp_blackout_bound_monotone_correspondence` | [view](3_printed_declarations/jlfp_blackout_bound_monotone.md) |
| `overheads_sbf_unit` | Lemma | `Prosa.Analysis.Facts.Model.Overheads.Sbf.Jlfp.overheads_sbf_unit` | `overheads_sbf_unit_correspondence` | [view](3_printed_declarations/overheads_sbf_unit.md) |
| `overheads_sbf_busy_valid` | Lemma | `Prosa.Analysis.Facts.Model.Overheads.Sbf.Jlfp.overheads_sbf_busy_valid` | `overheads_sbf_busy_valid_correspondence` | [view](3_printed_declarations/overheads_sbf_busy_valid.md) |

## Certificates

| Module | Role |
|---|---|
| [`OverheadsSbfJlfpCorrespondence`](4_correspondence/OverheadsSbfJlfpCorrespondence.v) | Definition and statement correspondences for `analysis/facts/model/overheads/sbf/jlfp.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
