(* Recomputes the authoritative `Check @name` fingerprints for model/task/sequentiality.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.model.task.sequentiality.
Goal True. idtac "BEGIN|prosa.model.task.sequentiality.sequential_tasks". Abort.
Check @prosa.model.task.sequentiality.sequential_tasks.
Goal True. idtac "END|prosa.model.task.sequentiality.sequential_tasks". Abort.
Goal True. idtac "BEGIN|prosa.model.task.sequentiality.prior_jobs_complete". Abort.
Check @prosa.model.task.sequentiality.prior_jobs_complete.
Goal True. idtac "END|prosa.model.task.sequentiality.prior_jobs_complete". Abort.
