(* Recomputes the authoritative `Check @name` fingerprints for model/priority/edf.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.model.priority.edf.
Goal True. idtac "BEGIN|prosa.model.priority.edf.EDF". Abort.
Check @prosa.model.priority.edf.EDF.
Goal True. idtac "END|prosa.model.priority.edf.EDF". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.edf.EDF_is_reflexive". Abort.
Check @prosa.model.priority.edf.EDF_is_reflexive.
Goal True. idtac "END|prosa.model.priority.edf.EDF_is_reflexive". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.edf.EDF_is_transitive". Abort.
Check @prosa.model.priority.edf.EDF_is_transitive.
Goal True. idtac "END|prosa.model.priority.edf.EDF_is_transitive". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.edf.EDF_is_total". Abort.
Check @prosa.model.priority.edf.EDF_is_total.
Goal True. idtac "END|prosa.model.priority.edf.EDF_is_total". Abort.
