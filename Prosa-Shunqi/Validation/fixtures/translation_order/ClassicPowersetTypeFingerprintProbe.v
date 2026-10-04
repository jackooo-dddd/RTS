(* Recomputes the authoritative `Check @name` fingerprints for classic/util/powerset.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.util.powerset.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop div path.
Goal True. idtac "BEGIN|prosa.classic.util.powerset.powerset". Abort.
Check @prosa.classic.util.powerset.powerset.
Goal True. idtac "END|prosa.classic.util.powerset.powerset". Abort.
Goal True. idtac "BEGIN|prosa.classic.util.powerset.mem_powerset". Abort.
Check @prosa.classic.util.powerset.mem_powerset.
Goal True. idtac "END|prosa.classic.util.powerset.mem_powerset". Abort.
