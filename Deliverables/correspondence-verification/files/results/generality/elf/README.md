# `results/generality/elf.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `elf_generalizes_gel` | Remark | `Prosa.Results.Generality.Elf.elf_generalizes_gel` | `elf_generalizes_gel_correspondence` | [view](3_printed_declarations/elf_generalizes_gel.md) |
| `elf_is_fixed_priority` | Remark | `Prosa.Results.Generality.Elf.elf_is_fixed_priority` | `elf_is_fixed_priority_correspondence` | [view](3_printed_declarations/elf_is_fixed_priority.md) |
| `elf_generalizes_fixed_priority` | Remark | `Prosa.Results.Generality.Elf.elf_generalizes_fixed_priority` | `elf_generalizes_fixed_priority_correspondence` | [view](3_printed_declarations/elf_generalizes_fixed_priority.md) |

## Certificates

| Module | Role |
|---|---|
| [`GeneralityElfCorrespondence`](4_correspondence/GeneralityElfCorrespondence.v) | Statement correspondences for `results/generality/elf.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
