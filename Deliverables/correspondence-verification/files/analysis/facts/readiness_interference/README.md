# `analysis/facts/readiness_interference.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `no_hep_ready_implies_no_another_hep_interference` | Lemma | `Prosa.Analysis.Facts.ReadinessInterference.no_hep_ready_implies_no_another_hep_interference` | `no_hep_ready_implies_no_another_hep_interference_correspondence` | [view](3_printed_declarations/no_hep_ready_implies_no_another_hep_interference.md) |
| `no_hep_ready_implies_no_service_inversion` | Lemma | `Prosa.Analysis.Facts.ReadinessInterference.no_hep_ready_implies_no_service_inversion` | `no_hep_ready_implies_no_service_inversion_correspondence` | [view](3_printed_declarations/no_hep_ready_implies_no_service_inversion.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsReadinessInterferenceCorrespondence`](4_correspondence/FactsReadinessInterferenceCorrespondence.v) | Statement certificates for `analysis/facts/readiness_interference.v`: for related processor states and schedules (the accepted two-sided Service relations of both certificate generations over the … |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `AdTrue`, `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
