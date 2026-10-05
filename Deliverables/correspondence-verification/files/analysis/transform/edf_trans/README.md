# `analysis/transform/edf_trans.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `earlier_deadline` | Definition | `Prosa.Analysis.Transform.EdfTrans.earlier_deadline` | `earlier_deadline_correspondence` | [view](3_printed_declarations/earlier_deadline.md) |
| `relevant_pstate` | Definition | `Prosa.Analysis.Transform.EdfTrans.relevant_pstate` | `relevant_pstate_correspondence` | [view](3_printed_declarations/relevant_pstate.md) |
| `find_swap_candidate` | Definition | `Prosa.Analysis.Transform.EdfTrans.find_swap_candidate` | `find_swap_candidate_correspondence` | [view](3_printed_declarations/find_swap_candidate.md) |
| `make_edf_at` | Definition | `Prosa.Analysis.Transform.EdfTrans.make_edf_at` | `make_edf_at_correspondence` | [view](3_printed_declarations/make_edf_at.md) |
| `edf_transform_prefix` | Definition | `Prosa.Analysis.Transform.EdfTrans.edf_transform_prefix` | `edf_transform_prefix_correspondence` | [view](3_printed_declarations/edf_transform_prefix.md) |
| `edf_transform` | Definition | `Prosa.Analysis.Transform.EdfTrans.edf_transform` | `edf_transform_correspondence` | [view](3_printed_declarations/edf_transform.md) |

## Certificates

| Module | Role |
|---|---|
| [`EdfTransCorrespondence`](4_correspondence/EdfTransCorrespondence.v) | Definition certificates for `analysis/transform/edf_trans.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
