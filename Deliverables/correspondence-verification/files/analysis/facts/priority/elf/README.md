# `analysis/facts/priority/elf.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `hep_job_elf_gel` | Remark | `Prosa.Analysis.Facts.Priority.Elf.hep_job_elf_gel` | `hep_job_elf_gel_correspondence` | [view](3_printed_declarations/hep_job_elf_gel.md) |
| `hep_job_arrival_elf` | Fact | `Prosa.Analysis.Facts.Priority.Elf.hep_job_arrival_elf` | `hep_job_arrival_elf_correspondence` | [view](3_printed_declarations/hep_job_arrival_elf.md) |
| `ELF_is_reflexive` | Lemma | `Prosa.Analysis.Facts.Priority.Elf.ELF_is_reflexive` | `ELF_is_reflexive_correspondence` | [view](3_printed_declarations/ELF_is_reflexive.md) |
| `ELF_is_transitive` | Lemma | `Prosa.Analysis.Facts.Priority.Elf.ELF_is_transitive` | `ELF_is_transitive_correspondence` | [view](3_printed_declarations/ELF_is_transitive.md) |
| `ELF_is_total` | Lemma | `Prosa.Analysis.Facts.Priority.Elf.ELF_is_total` | `ELF_is_total_correspondence` | [view](3_printed_declarations/ELF_is_total.md) |
| `ELF_is_JLFP_FP_compatible` | Lemma | `Prosa.Analysis.Facts.Priority.Elf.ELF_is_JLFP_FP_compatible` | `ELF_is_JLFP_FP_compatible_correspondence` | [view](3_printed_declarations/ELF_is_JLFP_FP_compatible.md) |
| `ELF_respects_sequential_tasks` | Lemma | `Prosa.Analysis.Facts.Priority.Elf.ELF_respects_sequential_tasks` | `ELF_respects_sequential_tasks_correspondence` | [view](3_printed_declarations/ELF_respects_sequential_tasks.md) |
| `ELF_implies_sequential_tasks` | Lemma | `Prosa.Analysis.Facts.Priority.Elf.ELF_implies_sequential_tasks` | `ELF_implies_sequential_tasks_correspondence` | [view](3_printed_declarations/ELF_implies_sequential_tasks.md) |

## Certificates

| Module | Role |
|---|---|
| [`FactsPriorityElfCorrespondence`](4_correspondence/FactsPriorityElfCorrespondence.v) | Statement correspondences for `analysis/facts/priority/elf.v`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `ArTrue`, `HEq`, `HEq_inst1`, `PdTrue`, `SubNatTrue`, `SvcSourceTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
