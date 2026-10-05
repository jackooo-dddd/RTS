# `analysis/definitions/service_inversion/readiness_aware.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `service_inversion` | Definition | `Prosa.Analysis.Definitions.ServiceInversion.ReadinessAware.service_inversion` | `service_inversion_correspondence` | [view](3_printed_declarations/service_inversion.md) |
| `cumulative_service_inversion` | Definition | `Prosa.Analysis.Definitions.ServiceInversion.ReadinessAware.cumulative_service_inversion` | `cumulative_service_inversion_correspondence` | [view](3_printed_declarations/cumulative_service_inversion.md) |
| `service_inversion_is_bounded` | Definition | `Prosa.Analysis.Definitions.ServiceInversion.ReadinessAware.service_inversion_is_bounded` | `service_inversion_is_bounded_correspondence` | [view](3_printed_declarations/service_inversion_is_bounded.md) |

## Certificates

None: every certificate module this file uses is shared.

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `AdTrue`, `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
