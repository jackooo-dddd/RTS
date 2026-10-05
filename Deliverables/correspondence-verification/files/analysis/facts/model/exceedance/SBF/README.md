# `analysis/facts/model/exceedance/SBF.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `eps_sbf` | Definition | `Prosa.Analysis.Facts.Model.Exceedance.SBF.eps_sbf` | `eps_sbf_correspondence` | [view](3_printed_declarations/eps_sbf.md) |
| `blackout_during_bounded` | Lemma | `Prosa.Analysis.Facts.Model.Exceedance.SBF.blackout_during_bounded` | `blackout_during_bounded_correspondence` | [view](3_printed_declarations/blackout_during_bounded.md) |
| `eps_sbf_is_valid` | Lemma | `Prosa.Analysis.Facts.Model.Exceedance.SBF.eps_sbf_is_valid` | `eps_sbf_is_valid_correspondence` | [view](3_printed_declarations/eps_sbf_is_valid.md) |
| `eps_sbf_is_unit` | Lemma | `Prosa.Analysis.Facts.Model.Exceedance.SBF.eps_sbf_is_unit` | `eps_sbf_is_unit_correspondence` | [view](3_printed_declarations/eps_sbf_is_unit.md) |

## Certificates

| Module | Role |
|---|---|
| [`ExceedanceSbfCorrespondence`](4_correspondence/ExceedanceSbfCorrespondence.v) | Definition and statement correspondences for `analysis/facts/model/exceedance/SBF.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
