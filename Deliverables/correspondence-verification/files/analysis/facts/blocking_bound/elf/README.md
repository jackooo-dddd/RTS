# `analysis/facts/blocking_bound/elf.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `nonpreemptive_segments_bounded_by_blocking` | Lemma | `Prosa.Analysis.Facts.BlockingBound.Elf.nonpreemptive_segments_bounded_by_blocking` | `nonpreemptive_segments_bounded_by_blocking_correspondence` | [view](3_printed_declarations/nonpreemptive_segments_bounded_by_blocking.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsBlockingBoundElfCorrespondence`](4_correspondence/FactsBlockingBoundElfCorrespondence.v) | Statement correspondence for `analysis/facts/blocking_bound/elf.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `PdTrue`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
