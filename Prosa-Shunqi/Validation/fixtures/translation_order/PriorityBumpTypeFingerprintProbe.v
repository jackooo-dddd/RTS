(* Recomputes the authoritative `Check @name` fingerprints for analysis/definitions/overheads/priority_bump.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.analysis.definitions.overheads.priority_bump.
(* display-only: a second `processor_state` in scope, as in the authoritative
   all-modules probe, so the overheads one prints qualified *)
Require Import prosa.model.processor.restricted_supply.
Goal True. idtac "BEGIN|prosa.analysis.definitions.overheads.priority_bump.priority_bump". Abort.
Check @prosa.analysis.definitions.overheads.priority_bump.priority_bump.
Goal True. idtac "END|prosa.analysis.definitions.overheads.priority_bump.priority_bump". Abort.
