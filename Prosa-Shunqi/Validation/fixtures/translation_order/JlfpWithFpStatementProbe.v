Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.JlfpWithFpSemanticSource.
Import JlfpWithFpSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Require Import prosa.behavior.all prosa.model.task.concept prosa.model.priority.classes prosa.model.aggregate.workload.
Require Import prosa.analysis.definitions.priority.classes.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.jlfp_with_fp.other_ep_task". Abort.
Check @other_ep_task.
Goal True. idtac "END|prosa.analysis.facts.priority.jlfp_with_fp.other_ep_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.jlfp_with_fp.hep_job_of_ep_other_task". Abort.
Check @hep_job_of_ep_other_task.
Goal True. idtac "END|prosa.analysis.facts.priority.jlfp_with_fp.hep_job_of_ep_other_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.jlfp_with_fp.hep_workload_from_other_ep_partitioned_by_tasks". Abort.
Print statement_hep_workload_from_other_ep_partitioned_by_tasks.
Goal True. idtac "END|prosa.analysis.facts.priority.jlfp_with_fp.hep_workload_from_other_ep_partitioned_by_tasks". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.jlfp_with_fp.from_hp_task". Abort.
Check @from_hp_task.
Goal True. idtac "END|prosa.analysis.facts.priority.jlfp_with_fp.from_hp_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.jlfp_with_fp.hep_from_hp_task". Abort.
Check @hep_from_hp_task.
Goal True. idtac "END|prosa.analysis.facts.priority.jlfp_with_fp.hep_from_hp_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.jlfp_with_fp.hep_from_ep_task". Abort.
Check @hep_from_ep_task.
Goal True. idtac "END|prosa.analysis.facts.priority.jlfp_with_fp.hep_from_ep_task". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.jlfp_with_fp.hep_hp_workload_hp". Abort.
Print statement_hep_hp_workload_hp.
Goal True. idtac "END|prosa.analysis.facts.priority.jlfp_with_fp.hep_hp_workload_hp". Abort.
Goal True. idtac "BEGIN|prosa.analysis.facts.priority.jlfp_with_fp.hep_workload_partitioning_taskwise". Abort.
Print statement_hep_workload_partitioning_taskwise.
Goal True. idtac "END|prosa.analysis.facts.priority.jlfp_with_fp.hep_workload_partitioning_taskwise". Abort.
