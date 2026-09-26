(* Recomputes the authoritative `Check @name` fingerprints for model/task/jitter.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.model.task.jitter.
Goal True. idtac "BEGIN|prosa.model.task.jitter.TaskJitter". Abort.
Check @prosa.model.task.jitter.TaskJitter.
Goal True. idtac "END|prosa.model.task.jitter.TaskJitter". Abort.
Goal True. idtac "BEGIN|prosa.model.task.jitter.valid_jitter". Abort.
Check @prosa.model.task.jitter.valid_jitter.
Goal True. idtac "END|prosa.model.task.jitter.valid_jitter". Abort.
Goal True. idtac "BEGIN|prosa.model.task.jitter.valid_jitter_bounds". Abort.
Check @prosa.model.task.jitter.valid_jitter_bounds.
Goal True. idtac "END|prosa.model.task.jitter.valid_jitter_bounds". Abort.
