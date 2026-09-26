(* Recomputes the authoritative `Check @name` fingerprints for infinite_jobs.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.analysis.definitions.infinite_jobs.
Goal True. idtac "BEGIN|prosa.analysis.definitions.infinite_jobs.infinite_jobs". Abort.
Check @prosa.analysis.definitions.infinite_jobs.infinite_jobs.
Goal True. idtac "END|prosa.analysis.definitions.infinite_jobs.infinite_jobs". Abort.
