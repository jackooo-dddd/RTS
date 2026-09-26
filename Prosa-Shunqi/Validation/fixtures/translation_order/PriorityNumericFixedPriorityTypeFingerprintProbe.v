(* Recomputes the authoritative `Check @name` fingerprints for model/priority/numeric_fixed_priority.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.model.priority.numeric_fixed_priority.
(* display-only: a second `TaskPriority` in scope (as in the authoritative
   all-modules probe, where implementation/definitions/task.v defines one),
   so the class prints qualified as in the evidence *)
Module DisplayOnly. Definition TaskPriority := tt. End DisplayOnly. Import DisplayOnly.
Goal True. idtac "BEGIN|prosa.model.priority.numeric_fixed_priority.TaskPriority". Abort.
Check @prosa.model.priority.numeric_fixed_priority.TaskPriority.
Goal True. idtac "END|prosa.model.priority.numeric_fixed_priority.TaskPriority". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.numeric_fixed_priority.NFPA_is_reflexive". Abort.
Check @prosa.model.priority.numeric_fixed_priority.NFPA_is_reflexive.
Goal True. idtac "END|prosa.model.priority.numeric_fixed_priority.NFPA_is_reflexive". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.numeric_fixed_priority.NFPA_is_transitive". Abort.
Check @prosa.model.priority.numeric_fixed_priority.NFPA_is_transitive.
Goal True. idtac "END|prosa.model.priority.numeric_fixed_priority.NFPA_is_transitive". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.numeric_fixed_priority.NFPA_is_total". Abort.
Check @prosa.model.priority.numeric_fixed_priority.NFPA_is_total.
Goal True. idtac "END|prosa.model.priority.numeric_fixed_priority.NFPA_is_total". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.numeric_fixed_priority.NFPD_is_reflexive". Abort.
Check @prosa.model.priority.numeric_fixed_priority.NFPD_is_reflexive.
Goal True. idtac "END|prosa.model.priority.numeric_fixed_priority.NFPD_is_reflexive". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.numeric_fixed_priority.NFPD_is_transitive". Abort.
Check @prosa.model.priority.numeric_fixed_priority.NFPD_is_transitive.
Goal True. idtac "END|prosa.model.priority.numeric_fixed_priority.NFPD_is_transitive". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.numeric_fixed_priority.NFPD_is_total". Abort.
Check @prosa.model.priority.numeric_fixed_priority.NFPD_is_total.
Goal True. idtac "END|prosa.model.priority.numeric_fixed_priority.NFPD_is_total". Abort.
