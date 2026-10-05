# `analysis/abstract/ideal/abstract_rta.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `nonpreemptive_interference_is_bounded` | Lemma | `Prosa.Analysis.Abstract.Ideal.AbstractRta.nonpreemptive_interference_is_bounded` | `nonpreemptive_interference_is_bounded_correspondence` | [view](3_printed_declarations/nonpreemptive_interference_is_bounded.md) |
| `uniprocessor_response_time_bound_ideal` | Theorem | `Prosa.Analysis.Abstract.Ideal.AbstractRta.uniprocessor_response_time_bound_ideal` | `uniprocessor_response_time_bound_ideal_correspondence` | [view](3_printed_declarations/uniprocessor_response_time_bound_ideal.md) |

## Certificates

| Module | Role |
|---|---|
| [`IdealAbstractRtaCorrespondence`](4_correspondence/IdealAbstractRtaCorrespondence.v) | Statement correspondences for `analysis/abstract/ideal/abstract_rta.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `AdTrue`, `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
