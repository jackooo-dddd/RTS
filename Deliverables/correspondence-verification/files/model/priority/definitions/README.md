# `model/priority/definitions.v`

| Rocq declaration | Kind | Lean declaration | Certificate | Printed |
|---|---|---|---|---|
| `FP_policy` | Class | `Prosa.Model.Priority.Definitions.FP_policy` | `pd_fp_import_certificate, pd_fp_export_certificate` | [view](3_printed_declarations/FP_policy.md) |
| `JLFP_policy` | Class | `Prosa.Model.Priority.Definitions.JLFP_policy` | `pd_jlfp_import_certificate, pd_jlfp_export_certificate` | [view](3_printed_declarations/JLFP_policy.md) |
| `JLDP_policy` | Class | `Prosa.Model.Priority.Definitions.JLDP_policy` | `pd_jldp_import_certificate, pd_jldp_export_certificate` | [view](3_printed_declarations/JLDP_policy.md) |
| `reflexive_priorities` | Definition | `Prosa.Model.Priority.Definitions.reflexive_priorities` | `pd_reflexive_priorities_certificate` | [view](3_printed_declarations/reflexive_priorities.md) |
| `transitive_priorities` | Definition | `Prosa.Model.Priority.Definitions.transitive_priorities` | `pd_transitive_priorities_certificate` | [view](3_printed_declarations/transitive_priorities.md) |
| `total_priorities` | Definition | `Prosa.Model.Priority.Definitions.total_priorities` | `pd_total_priorities_certificate` | [view](3_printed_declarations/total_priorities.md) |
| `reflexive_job_priorities` | Definition | `Prosa.Model.Priority.Definitions.reflexive_job_priorities` | `pd_reflexive_job_priorities_certificate` | [view](3_printed_declarations/reflexive_job_priorities.md) |
| `transitive_job_priorities` | Definition | `Prosa.Model.Priority.Definitions.transitive_job_priorities` | `pd_transitive_job_priorities_certificate` | [view](3_printed_declarations/transitive_job_priorities.md) |
| `total_job_priorities` | Definition | `Prosa.Model.Priority.Definitions.total_job_priorities` | `pd_total_job_priorities_certificate` | [view](3_printed_declarations/total_job_priorities.md) |
| `policy_respects_sequential_tasks` | Definition | `Prosa.Model.Priority.Definitions.policy_respects_sequential_tasks` | `pd_policy_respects_sequential_tasks_certificate` | [view](3_printed_declarations/policy_respects_sequential_tasks.md) |
| `policy_is_FIFO` | Definition | `Prosa.Model.Priority.Definitions.policy_is_FIFO` | `pd_policy_is_FIFO_certificate` | [view](3_printed_declarations/policy_is_FIFO.md) |
| `reflexive_task_priorities` | Definition | `Prosa.Model.Priority.Definitions.reflexive_task_priorities` | `pd_reflexive_task_priorities_certificate` | [view](3_printed_declarations/reflexive_task_priorities.md) |
| `transitive_task_priorities` | Definition | `Prosa.Model.Priority.Definitions.transitive_task_priorities` | `pd_transitive_task_priorities_certificate` | [view](3_printed_declarations/transitive_task_priorities.md) |
| `total_task_priorities` | Definition | `Prosa.Model.Priority.Definitions.total_task_priorities` | `pd_total_task_priorities_certificate` | [view](3_printed_declarations/total_task_priorities.md) |
| `antisymmetric_over_taskset` | Definition | `Prosa.Model.Priority.Definitions.antisymmetric_over_taskset` | `pd_antisymmetric_over_taskset_certificate` | [view](3_printed_declarations/antisymmetric_over_taskset.md) |
| `another_hep_job` | Definition | `Prosa.Model.Priority.Definitions.another_hep_job` | `pd_another_hep_job_certificate` | [view](3_printed_declarations/another_hep_job.md) |
| `another_task_hep_job` | Definition | `Prosa.Model.Priority.Definitions.another_task_hep_job` | `pd_another_task_hep_job_certificate` | [view](3_printed_declarations/another_task_hep_job.md) |
| `another_hep_job_of_same_task` | Definition | `Prosa.Model.Priority.Definitions.another_hep_job_of_same_task` | `pd_another_hep_job_of_same_task_certificate` | [view](3_printed_declarations/another_hep_job_of_same_task.md) |
| `hp_task` | Definition | `Prosa.Model.Priority.Definitions.hp_task` | `pd_hp_task_certificate` | [view](3_printed_declarations/hp_task.md) |
| `ep_task` | Definition | `Prosa.Model.Priority.Definitions.ep_task` | `pd_ep_task_certificate` | [view](3_printed_declarations/ep_task.md) |

## Certificates

| Module | Role |
|---|---|
| [`PriorityDerived`](4_correspondence/PriorityDerived.v) | Proves or defines `pd_another_hep_job_certificate`, `pd_another_task_hep_job_certificate`, `pd_another_hep_job_of_same_task_certificate` and 2 more. |
| [`PriorityDynamicOrder`](4_correspondence/PriorityDynamicOrder.v) | Proves or defines `pd_reflexive_priorities_certificate`, `pd_transitive_priorities_certificate`, `pd_total_priorities_certificate`. |
| [`PriorityListAdapter`](4_correspondence/PriorityListAdapter.v) | Proves or defines `PdBoolTruth`, `pd_bool_prop_to_truth`, `pd_truth_to_strict_bool_prop` and 14 more. |
| [`PriorityPolicyProperties`](4_correspondence/PriorityPolicyProperties.v) | Proves or defines `pd_policy_is_FIFO_certificate`, `pd_policy_respects_sequential_tasks_certificate`. |
| [`PriorityStaticOrder`](4_correspondence/PriorityStaticOrder.v) | The nine order-property definitions are related by the actual policy field operation. |
| [`PriorityAntisymmetric`](4_correspondence/PriorityAntisymmetric.v) | Proves or defines `pd_antisymmetric_over_taskset_certificate`. |

Shared modules used: [`4_correspondence/shared.md`](4_correspondence/shared.md).

## Assumptions ([`assumption_summary.json`](5_assumptions/assumption_summary.json))

| Category | Items |
|---|---|
| Prop/SProp foundation | `PropSPropFoundation.interpret_strict` |
| Imported Lean axioms | — |
| Definitional UIP | `HEq_inst1`, `PdTrue`, `SubNatTrue`, `True`, `eq`, `eq_inst1` |
| Rocq primitives | — |
