# `analysis/abstract/restricted_supply/abstract_seq_rta.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `IBF_P_bounds_interference` | Lemma | `Prosa.Analysis.Abstract.RestrictedSupply.AbstractSeqRta.IBF_P_bounds_interference` | `IBF_P_bounds_interference_correspondence` | [view](3_printed_declarations/IBF_P_bounds_interference.md) |
| `sol_seq_rs_equation_impl_sol_rs_equation` | Lemma | `Prosa.Analysis.Abstract.RestrictedSupply.AbstractSeqRta.sol_seq_rs_equation_impl_sol_rs_equation` | `sol_seq_rs_equation_impl_sol_rs_equation_correspondence` | [view](3_printed_declarations/sol_seq_rs_equation_impl_sol_rs_equation.md) |
| `uniprocessor_response_time_bound_restricted_supply_seq` | Theorem | `Prosa.Analysis.Abstract.RestrictedSupply.AbstractSeqRta.uniprocessor_response_time_bound_restricted_supply_seq` | `uniprocessor_response_time_bound_restricted_supply_seq_correspondence` | [view](3_printed_declarations/uniprocessor_response_time_bound_restricted_supply_seq.md) |

## Certificates

| Module | Role |
|---|---|
| [`RsAbstractSeqRtaCorrespondence`](4_correspondence/RsAbstractSeqRtaCorrespondence.v) | Statement correspondences for `analysis/abstract/restricted_supply/abstract_seq_rta.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `AdTrue`, `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
