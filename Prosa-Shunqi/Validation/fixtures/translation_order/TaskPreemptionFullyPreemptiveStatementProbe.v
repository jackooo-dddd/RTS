Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.TaskPreemptionFullyPreemptiveSemanticSource.
Import TaskPreemptionFullyPreemptiveSemanticSource.
(* display-only: the same imports as the extracted module, so names print unqualified *)
Require Import prosa.TaskPreemptionParametersSemanticSource.
Import TaskPreemptionParametersSemanticSource.
Goal True. idtac "BEGIN|prosa.model.task.preemption.fully_preemptive.fully_preemptive_task_model". Abort.
Check @fully_preemptive_task_model.
Goal True. idtac "END|prosa.model.task.preemption.fully_preemptive.fully_preemptive_task_model". Abort.
