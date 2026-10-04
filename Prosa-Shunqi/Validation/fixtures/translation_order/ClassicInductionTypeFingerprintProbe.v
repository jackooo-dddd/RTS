(* Recomputes the authoritative `Check @name` fingerprints for classic/util/induction.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.util.induction.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop div path.
Goal True. idtac "BEGIN|prosa.classic.util.induction.strong_ind". Abort.
Check @prosa.classic.util.induction.strong_ind.
Goal True. idtac "END|prosa.classic.util.induction.strong_ind". Abort.
Goal True. idtac "BEGIN|prosa.classic.util.induction.leq_as_delta". Abort.
Check @prosa.classic.util.induction.leq_as_delta.
Goal True. idtac "END|prosa.classic.util.induction.leq_as_delta". Abort.
