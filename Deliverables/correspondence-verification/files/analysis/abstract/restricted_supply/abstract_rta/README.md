# `analysis/abstract/restricted_supply/abstract_rta.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `blackout_impl_interference` | Lemma | `Prosa.Analysis.Abstract.RestrictedSupply.AbstractRta.blackout_impl_interference` | `blackout_impl_interference_correspondence` | [view](3_printed_declarations/blackout_impl_interference.md) |
| `blackout_plus_local_is_interference` | Lemma | `Prosa.Analysis.Abstract.RestrictedSupply.AbstractRta.blackout_plus_local_is_interference` | `blackout_plus_local_is_interference_correspondence` | [view](3_printed_declarations/blackout_plus_local_is_interference.md) |
| `blackout_plus_local_is_interference_cumul` | Corollary | `Prosa.Analysis.Abstract.RestrictedSupply.AbstractRta.blackout_plus_local_is_interference_cumul` | `blackout_plus_local_is_interference_cumul_correspondence` | [view](3_printed_declarations/blackout_plus_local_is_interference_cumul.md) |
| `cumulative_job_interference_bound` | Corollary | `Prosa.Analysis.Abstract.RestrictedSupply.AbstractRta.cumulative_job_interference_bound` | `cumulative_job_interference_bound_correspondence` | [view](3_printed_declarations/cumulative_job_interference_bound.md) |
| `no_intra_interference_after_F` | Lemma | `Prosa.Analysis.Abstract.RestrictedSupply.AbstractRta.no_intra_interference_after_F` | `no_intra_interference_after_F_correspondence` | [view](3_printed_declarations/no_intra_interference_after_F.md) |
| `IBF_P_bounds_interference` | Lemma | `Prosa.Analysis.Abstract.RestrictedSupply.AbstractRta.IBF_P_bounds_interference` | `IBF_P_bounds_interference_correspondence` | [view](3_printed_declarations/IBF_P_bounds_interference.md) |
| `IBF_NP_bounds_interference` | Lemma | `Prosa.Analysis.Abstract.RestrictedSupply.AbstractRta.IBF_NP_bounds_interference` | `IBF_NP_bounds_interference_correspondence` | [view](3_printed_declarations/IBF_NP_bounds_interference.md) |
| `IBF_P_sol_le_IBF_NP` | Lemma | `Prosa.Analysis.Abstract.RestrictedSupply.AbstractRta.IBF_P_sol_le_IBF_NP` | `IBF_P_sol_le_IBF_NP_correspondence` | [view](3_printed_declarations/IBF_P_sol_le_IBF_NP.md) |
| `max_in_rs_hypothesis_impl_max_in_arta_hypothesis` | Lemma | `Prosa.Analysis.Abstract.RestrictedSupply.AbstractRta.max_in_rs_hypothesis_impl_max_in_arta_hypothesis` | `max_in_rs_hypothesis_impl_max_in_arta_hypothesis_correspondence` | [view](3_printed_declarations/max_in_rs_hypothesis_impl_max_in_arta_hypothesis.md) |
| `uniprocessor_response_time_bound_restricted_supply` | Theorem | `Prosa.Analysis.Abstract.RestrictedSupply.AbstractRta.uniprocessor_response_time_bound_restricted_supply` | `uniprocessor_response_time_bound_restricted_supply_correspondence` | [view](3_printed_declarations/uniprocessor_response_time_bound_restricted_supply.md) |

## Certificates

| Module | Role |
|---|---|
| [`RsAbstractRtaCorrespondence`](4_correspondence/RsAbstractRtaCorrespondence.v) | Statement correspondences for `analysis/abstract/restricted_supply/abstract_rta.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `AdTrue`, `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
