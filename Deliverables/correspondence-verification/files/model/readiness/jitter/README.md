# `model/readiness/jitter.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `JobJitter` | Class | `Prosa.Model.Readiness.Jitter.JobJitter` | `JobJitter_source_total, JobJitter_target_total, JobJitter_source_roundtrip` | [view](3_printed_declarations/JobJitter.md) |
| `is_released` | Definition | `Prosa.Model.Readiness.Jitter.is_released` | `is_released_correspondence` | [view](3_printed_declarations/is_released.md) |

## Certificates

| Module | Role |
|---|---|
| [`JitterReadyCorrespondence`](4_correspondence/JitterReadyCorrespondence.v) | Reusable structural relation for a law with Boolean antecedent and consequent. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
