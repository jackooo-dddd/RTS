(* Recomputes the authoritative `Check @name` fingerprints for model/priority/gel.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.model.priority.gel.
(* display-only: the source's own util/int import, so MathComp's int prints as in the evidence *)
Require Import prosa.util.int.
Goal True. idtac "BEGIN|prosa.model.priority.gel.offset". Abort.
Check @prosa.model.priority.gel.offset.
Goal True. idtac "END|prosa.model.priority.gel.offset". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.gel.PriorityPoint". Abort.
Check @prosa.model.priority.gel.PriorityPoint.
Goal True. idtac "END|prosa.model.priority.gel.PriorityPoint". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.gel.job_priority_point". Abort.
Check @prosa.model.priority.gel.job_priority_point.
Goal True. idtac "END|prosa.model.priority.gel.job_priority_point". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.gel.GEL". Abort.
Check @prosa.model.priority.gel.GEL.
Goal True. idtac "END|prosa.model.priority.gel.GEL". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.gel.GEL_is_reflexive". Abort.
Check @prosa.model.priority.gel.GEL_is_reflexive.
Goal True. idtac "END|prosa.model.priority.gel.GEL_is_reflexive". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.gel.GEL_is_transitive". Abort.
Check @prosa.model.priority.gel.GEL_is_transitive.
Goal True. idtac "END|prosa.model.priority.gel.GEL_is_transitive". Abort.
Goal True. idtac "BEGIN|prosa.model.priority.gel.GEL_is_total". Abort.
Check @prosa.model.priority.gel.GEL_is_total.
Goal True. idtac "END|prosa.model.priority.gel.GEL_is_total". Abort.
