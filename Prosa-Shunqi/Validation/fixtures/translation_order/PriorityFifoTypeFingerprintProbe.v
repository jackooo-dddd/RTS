(* Recomputes the authoritative `Check @name` fingerprints for model/priority/fifo.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.model.priority.fifo.
Goal True. idtac "BEGIN|prosa.model.priority.fifo.FIFO". Abort.
Check @prosa.model.priority.fifo.FIFO.
Goal True. idtac "END|prosa.model.priority.fifo.FIFO". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.fifo.FIFO_is_reflexive". Abort.
Check @prosa.model.priority.fifo.FIFO_is_reflexive.
Goal True. idtac "END|prosa.model.priority.fifo.FIFO_is_reflexive". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.fifo.FIFO_is_transitive". Abort.
Check @prosa.model.priority.fifo.FIFO_is_transitive.
Goal True. idtac "END|prosa.model.priority.fifo.FIFO_is_transitive". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.fifo.FIFO_is_total". Abort.
Check @prosa.model.priority.fifo.FIFO_is_total.
Goal True. idtac "END|prosa.model.priority.fifo.FIFO_is_total". Abort.
