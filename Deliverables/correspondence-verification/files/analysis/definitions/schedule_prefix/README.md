# `analysis/definitions/schedule_prefix.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `identical_prefix` | Definition | `Prosa.Analysis.Definitions.SchedulePrefix.identical_prefix` | `identical_prefix_correspondence` | [view](3_printed_declarations/identical_prefix.md) |
| `identical_prefix_scheduled_at` | Fact | `Prosa.Analysis.Definitions.SchedulePrefix.identical_prefix_scheduled_at` | `identical_prefix_scheduled_at_statement_correspondence` | [view](3_printed_declarations/identical_prefix_scheduled_at.md) |
| `identical_prefix_inclusion` | Fact | `Prosa.Analysis.Definitions.SchedulePrefix.identical_prefix_inclusion` | `identical_prefix_inclusion_statement_correspondence` | [view](3_printed_declarations/identical_prefix_inclusion.md) |

## Certificates

| Module | Role |
|---|---|
| [`SchedulePrefixExactTypeGuards`](4_correspondence/SchedulePrefixExactTypeGuards.v) | These checks bind the independently proved structural relations to the two official Rocq theorem types and two exact imported compiled Lean theorem types. |
| [`SchedulePrefixOperations`](4_correspondence/SchedulePrefixOperations.v) | Minimal artifact-local replay of the already certified finite Boolean existential construction from ServiceScheduleOperations.v. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | `Classical_choice`, `Quot_sound`, `propext` |
| Definitional UIP | `HEq`, `HEq_inst1`, `PrefixSourceTrue`, `SubNatTrue`, `SvcTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | `PrimInt63.*` |
