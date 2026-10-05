# `analysis/facts/readiness/basic.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `basic_readiness_nonclairvoyance` | Fact | `Prosa.Analysis.Facts.Readiness.Basic.basic_readiness_nonclairvoyance` | `basic_readiness_nonclairvoyance_correspondence` | [view](3_printed_declarations/basic_readiness_nonclairvoyance.md) |
| `basic_readiness_compliance` | Lemma | `Prosa.Analysis.Facts.Readiness.Basic.basic_readiness_compliance` | `basic_readiness_compliance_correspondence` | [view](3_printed_declarations/basic_readiness_compliance.md) |
| `basic_readiness_is_work_bearing_readiness` | Fact | `Prosa.Analysis.Facts.Readiness.Basic.basic_readiness_is_work_bearing_readiness` | `basic_readiness_is_work_bearing_readiness_correspondence` | [view](3_printed_declarations/basic_readiness_is_work_bearing_readiness.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsReadinessBasicCorrespondence`](4_correspondence/FactsReadinessBasicCorrespondence.v) | Statement correspondences for `analysis/facts/readiness/basic.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
