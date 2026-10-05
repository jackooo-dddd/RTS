# `analysis/definitions/readiness_interference.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `some_hep_job_ready` | Definition | `Prosa.Analysis.Definitions.ReadinessInterference.some_hep_job_ready` | `some_hep_job_ready_correspondence` | [view](3_printed_declarations/some_hep_job_ready.md) |
| `cumulative_readiness_interference` | Definition | `Prosa.Analysis.Definitions.ReadinessInterference.cumulative_readiness_interference` | `cumulative_readiness_interference_correspondence` | [view](3_printed_declarations/cumulative_readiness_interference.md) |
| `readiness_interference_is_bounded` | Definition | `Prosa.Analysis.Definitions.ReadinessInterference.readiness_interference_is_bounded` | `readiness_interference_is_bounded_correspondence` | [view](3_printed_declarations/readiness_interference_is_bounded.md) |

## Certificates

None: every certificate module this file uses is shared.

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `AdTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
