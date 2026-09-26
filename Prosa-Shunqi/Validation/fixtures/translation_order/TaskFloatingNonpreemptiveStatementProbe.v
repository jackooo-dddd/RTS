Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.TaskFloatingNonpreemptiveSemanticSource.
Import TaskFloatingNonpreemptiveSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
Require Import prosa.TaskPreemptionParametersSemanticSource.
Import TaskPreemptionParametersSemanticSource.
Require Import prosa.LimitedPreemptiveSemanticSource.
Import LimitedPreemptiveSemanticSource.
Goal True. idtac "BEGIN|prosa.model.task.preemption.floating_nonpreemptive.job_respects_task_max_np_segment". Abort.
Check @job_respects_task_max_np_segment.
Goal True. idtac "END|prosa.model.task.preemption.floating_nonpreemptive.job_respects_task_max_np_segment". Abort.
Goal True. idtac "BEGIN|prosa.model.task.preemption.floating_nonpreemptive.valid_model_with_floating_nonpreemptive_regions". Abort.
Check @valid_model_with_floating_nonpreemptive_regions.
Goal True. idtac "END|prosa.model.task.preemption.floating_nonpreemptive.valid_model_with_floating_nonpreemptive_regions". Abort.
