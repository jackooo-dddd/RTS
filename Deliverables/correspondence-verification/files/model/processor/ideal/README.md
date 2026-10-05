# `model/processor/ideal.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `processor_state` | Definition | `Prosa.Model.Processor.Ideal.processor_state` | `ideal_processor_state_correspondence` | [view](3_printed_declarations/processor_state.md) |
| `ideal_is_idle` | Definition | `Prosa.Model.Processor.Ideal.ideal_is_idle` | `ideal_is_idle_correspondence` | [view](3_printed_declarations/ideal_is_idle.md) |

## Certificates

| Module | Role |
|---|---|
| [`IdealBaseAdapter`](4_correspondence/IdealBaseAdapter.v) | Proves or defines `ideal_false_elim`, `ideal_false_to_strict`, `ideal_coq_false_to_target` and 23 more. |
| [`IdealExactTypeGuards`](4_correspondence/IdealExactTypeGuards.v) | No description in the module. |
| [`IdealCorrespondence`](4_correspondence/IdealCorrespondence.v) | The concrete Option/Unit carriers are related by constructor-preserving maps, not by claiming Rocq and imported Lean datatypes are identical. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `IdealTrue`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
