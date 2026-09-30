(* Recomputes the authoritative `Check @name` fingerprints for implementation/definitions/task.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.implementation.definitions.task.
(* display-only: the class modules are re-imported after the file, as in the authoritative print environment,
   so the class names print unqualified and the same-named instances of this file print qualified *)
Import prosa.model.task.concept prosa.behavior.job.
Goal True. idtac "BEGIN|prosa.implementation.definitions.task.concrete_task". Abort.
Check @prosa.implementation.definitions.task.concrete_task.
Goal True. idtac "END|prosa.implementation.definitions.task.concrete_task". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.task.task_eqdef". Abort.
Check @prosa.implementation.definitions.task.task_eqdef.
Goal True. idtac "END|prosa.implementation.definitions.task.task_eqdef". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.task.eqn_task". Abort.
Check @prosa.implementation.definitions.task.eqn_task.
Goal True. idtac "END|prosa.implementation.definitions.task.eqn_task". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.task.concrete_job". Abort.
Check @prosa.implementation.definitions.task.concrete_job.
Goal True. idtac "END|prosa.implementation.definitions.task.concrete_job". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.task.get_arrival_curve_prefix". Abort.
Check @prosa.implementation.definitions.task.get_arrival_curve_prefix.
Goal True. idtac "END|prosa.implementation.definitions.task.get_arrival_curve_prefix". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.task.concrete_max_arrivals". Abort.
Check @prosa.implementation.definitions.task.concrete_max_arrivals.
Goal True. idtac "END|prosa.implementation.definitions.task.concrete_max_arrivals". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.task.job_eqdef". Abort.
Check @prosa.implementation.definitions.task.job_eqdef.
Goal True. idtac "END|prosa.implementation.definitions.task.job_eqdef". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.task.eqn_job". Abort.
Check @prosa.implementation.definitions.task.eqn_job.
Goal True. idtac "END|prosa.implementation.definitions.task.eqn_job". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.task.TaskCost". Abort.
Check @prosa.implementation.definitions.task.TaskCost.
Goal True. idtac "END|prosa.implementation.definitions.task.TaskCost". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.task.TaskPriority". Abort.
Check @prosa.implementation.definitions.task.TaskPriority.
Goal True. idtac "END|prosa.implementation.definitions.task.TaskPriority". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.task.TaskDeadline". Abort.
Check @prosa.implementation.definitions.task.TaskDeadline.
Goal True. idtac "END|prosa.implementation.definitions.task.TaskDeadline". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.task.ConcreteMaxArrivals". Abort.
Check @prosa.implementation.definitions.task.ConcreteMaxArrivals.
Goal True. idtac "END|prosa.implementation.definitions.task.ConcreteMaxArrivals". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.task.JobTask". Abort.
Check @prosa.implementation.definitions.task.JobTask.
Goal True. idtac "END|prosa.implementation.definitions.task.JobTask". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.task.JobArrival". Abort.
Check @prosa.implementation.definitions.task.JobArrival.
Goal True. idtac "END|prosa.implementation.definitions.task.JobArrival". Abort.
Goal True. idtac "BEGIN|prosa.implementation.definitions.task.JobCost". Abort.
Check @prosa.implementation.definitions.task.JobCost.
Goal True. idtac "END|prosa.implementation.definitions.task.JobCost". Abort.
