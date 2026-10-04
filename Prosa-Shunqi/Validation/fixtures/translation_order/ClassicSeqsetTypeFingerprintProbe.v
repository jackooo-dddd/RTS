(* Recomputes the authoritative `Check @name` fingerprints for classic/util/seqset.v. *)
Set Warnings "-notation-overridden,-missing-proof-command".
Set Printing Width 100000.
Require Import prosa.classic.util.seqset.
From mathcomp Require Import ssreflect ssrbool ssrfun eqtype ssrnat seq fintype bigop div path.
Goal True. idtac "BEGIN|prosa.classic.util.seqset.set_mem". Abort.
Check @prosa.classic.util.seqset.set_mem.
Goal True. idtac "END|prosa.classic.util.seqset.set_mem". Abort.
Goal True. idtac "BEGIN|prosa.classic.util.seqset.set_card". Abort.
Check @prosa.classic.util.seqset.set_card.
Goal True. idtac "END|prosa.classic.util.seqset.set_card". Abort.
