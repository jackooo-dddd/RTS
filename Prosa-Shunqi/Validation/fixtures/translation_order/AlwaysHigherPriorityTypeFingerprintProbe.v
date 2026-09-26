(* Recomputes the authoritative `Check @name` fingerprints for analysis/definitions/always_higher_priority.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.analysis.definitions.always_higher_priority.
Goal True. idtac "BEGIN|prosa.analysis.definitions.always_higher_priority.always_higher_priority". Abort.
Check @prosa.analysis.definitions.always_higher_priority.always_higher_priority.
Goal True. idtac "END|prosa.analysis.definitions.always_higher_priority.always_higher_priority". Abort.
Goal True. idtac "BEGIN|prosa.analysis.definitions.always_higher_priority.always_higher_priority_jlfp". Abort.
Check @prosa.analysis.definitions.always_higher_priority.always_higher_priority_jlfp.
Goal True. idtac "END|prosa.analysis.definitions.always_higher_priority.always_higher_priority_jlfp". Abort.
