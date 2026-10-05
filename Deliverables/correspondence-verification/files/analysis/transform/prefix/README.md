# `analysis/transform/prefix.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `prefix_map` | Fixpoint | `Prosa.Analysis.Transform.Prefix.prefix_map` | `prefix_map_correspondence` | [view](3_printed_declarations/prefix_map.md) |
| `prefix_map_property_invariance` | Lemma | `Prosa.Analysis.Transform.Prefix.prefix_map_property_invariance` | `prefix_map_property_invariance_correspondence` | [view](3_printed_declarations/prefix_map_property_invariance.md) |
| `prefix_map_pointwise_property` | Lemma | `Prosa.Analysis.Transform.Prefix.prefix_map_pointwise_property` | `prefix_map_pointwise_property_correspondence` | [view](3_printed_declarations/prefix_map_pointwise_property.md) |

## Certificates

| Module | Role |
|---|---|
| [`TransformPrefixCorrespondence`](4_correspondence/TransformPrefixCorrespondence.v) | Certificates for `analysis/transform/prefix.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
