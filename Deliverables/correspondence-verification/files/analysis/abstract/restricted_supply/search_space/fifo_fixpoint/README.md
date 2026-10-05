# `analysis/abstract/restricted_supply/search_space/fifo_fixpoint.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `soln_abstract_response_time_recurrence` | Lemma | `Prosa.Analysis.Abstract.RestrictedSupply.SearchSpace.FifoFixpoint.soln_abstract_response_time_recurrence` | `soln_abstract_response_time_recurrence_correspondence` | [view](3_printed_declarations/soln_abstract_response_time_recurrence.md) |

## Certificates

| Module | Role |
|---|---|
| [`RsIwHelpers`](4_correspondence/RsIwHelpers.v) | Helper-only copy of the accepted certificates/analysis_abstract_restricted_supply_iw_instantiation/ RsIwInstantiationCorrespondence.v (re-bound to this export), truncated before its statement … |
| [`FifoFixpointCorrespondence`](4_correspondence/FifoFixpointCorrespondence.v) | Statement correspondence for `analysis/abstract/restricted_supply/search_space/fifo_fixpoint.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
