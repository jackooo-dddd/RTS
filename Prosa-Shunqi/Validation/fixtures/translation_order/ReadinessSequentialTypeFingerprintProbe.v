(* Displays the named source-local instance of model/readiness/sequential.v
   (the file has no inventory declarations; the instance constant remains). *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.model.readiness.sequential.
Goal True. idtac "BEGIN|prosa.model.readiness.sequential.sequential_ready_instance". Abort.
Check @prosa.model.readiness.sequential.sequential_ready_instance.
Goal True. idtac "END|prosa.model.readiness.sequential.sequential_ready_instance". Abort.
