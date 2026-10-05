# `analysis/facts/SBF.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `valid_pred_sbf_switch_predicate` | Lemma | `Prosa.Analysis.Facts.SBF.valid_pred_sbf_switch_predicate` | `valid_pred_sbf_switch_predicate_correspondence` | [view](3_printed_declarations/valid_pred_sbf_switch_predicate.md) |
| `blackout_during_bound_SBF` | Lemma | `Prosa.Analysis.Facts.SBF.blackout_during_bound_SBF` | `blackout_during_bound_SBF_correspondence` | [view](3_printed_declarations/blackout_during_bound_SBF.md) |
| `complement_SBF_monotone` | Lemma | `Prosa.Analysis.Facts.SBF.complement_SBF_monotone` | `complement_SBF_monotone_correspondence` | [view](3_printed_declarations/complement_SBF_monotone.md) |

## Certificates

| Module | Role |
|---|---|
| [`SbfFactsCorrespondence`](4_correspondence/SbfFactsCorrespondence.v) | Statement correspondences for the three lemmas of `analysis/facts/SBF.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
