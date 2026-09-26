Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.InterferenceSemanticSource.
Import InterferenceSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
Goal True. idtac "BEGIN|prosa.analysis.definitions.interference.hp_task_interference". Abort.
Check @hp_task_interference.
Goal True. idtac "END|prosa.analysis.definitions.interference.hp_task_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.interference.ep_task_hep_job". Abort.
Check @ep_task_hep_job.
Goal True. idtac "END|prosa.analysis.definitions.interference.ep_task_hep_job". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.interference.other_ep_task_hep_job". Abort.
Check @other_ep_task_hep_job.
Goal True. idtac "END|prosa.analysis.definitions.interference.other_ep_task_hep_job". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.interference.hep_job_from_other_ep_task_interference". Abort.
Check @hep_job_from_other_ep_task_interference.
Goal True. idtac "END|prosa.analysis.definitions.interference.hep_job_from_other_ep_task_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.interference.hp_task_hep_job". Abort.
Check @hp_task_hep_job.
Goal True. idtac "END|prosa.analysis.definitions.interference.hp_task_hep_job". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.interference.hep_job_from_hp_task_interference". Abort.
Check @hep_job_from_hp_task_interference.
Goal True. idtac "END|prosa.analysis.definitions.interference.hep_job_from_hp_task_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.interference.cumulative_interference_from_hep_jobs_from_hp_tasks". Abort.
Check @cumulative_interference_from_hep_jobs_from_hp_tasks.
Goal True. idtac "END|prosa.analysis.definitions.interference.cumulative_interference_from_hep_jobs_from_hp_tasks". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.interference.cumulative_interference_from_hep_jobs_from_other_ep_tasks". Abort.
Check @cumulative_interference_from_hep_jobs_from_other_ep_tasks.
Goal True. idtac "END|prosa.analysis.definitions.interference.cumulative_interference_from_hep_jobs_from_other_ep_tasks". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.interference.another_hep_job_interference". Abort.
Check @another_hep_job_interference.
Goal True. idtac "END|prosa.analysis.definitions.interference.another_hep_job_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.interference.another_task_hep_job_interference". Abort.
Check @another_task_hep_job_interference.
Goal True. idtac "END|prosa.analysis.definitions.interference.another_task_hep_job_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.interference.another_hep_job_of_same_task_interference". Abort.
Check @another_hep_job_of_same_task_interference.
Goal True. idtac "END|prosa.analysis.definitions.interference.another_hep_job_of_same_task_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.interference.other_hep_jobs_interfering_workload". Abort.
Check @other_hep_jobs_interfering_workload.
Goal True. idtac "END|prosa.analysis.definitions.interference.other_hep_jobs_interfering_workload". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.interference.cumulative_another_hep_job_interference". Abort.
Check @cumulative_another_hep_job_interference.
Goal True. idtac "END|prosa.analysis.definitions.interference.cumulative_another_hep_job_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.interference.cumulative_another_task_hep_job_interference". Abort.
Check @cumulative_another_task_hep_job_interference.
Goal True. idtac "END|prosa.analysis.definitions.interference.cumulative_another_task_hep_job_interference". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.interference.cumulative_other_hep_jobs_interfering_workload". Abort.
Check @cumulative_other_hep_jobs_interfering_workload.
Goal True. idtac "END|prosa.analysis.definitions.interference.cumulative_other_hep_jobs_interfering_workload". Abort.
