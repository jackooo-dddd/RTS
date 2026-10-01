(* Recomputes the authoritative `Check @name` fingerprints for classic/model/time.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.model.time.
Goal True. idtac "BEGIN|prosa.classic.model.time.Time.time". Abort.
Check @prosa.classic.model.time.Time.time.
Goal True. idtac "END|prosa.classic.model.time.Time.time". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.time.Time.duration". Abort.
Check @prosa.classic.model.time.Time.duration.
Goal True. idtac "END|prosa.classic.model.time.Time.duration". Abort.
Goal True. idtac "BEGIN|prosa.classic.model.time.Time.instant". Abort.
Check @prosa.classic.model.time.Time.instant.
Goal True. idtac "END|prosa.classic.model.time.Time.instant". Abort.
