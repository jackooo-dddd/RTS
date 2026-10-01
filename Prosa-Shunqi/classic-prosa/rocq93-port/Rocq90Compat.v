(** Compatibility prelude for compiling ProsaBuddy's classic Prosa (written for
    Rocq 9.0.1 + MathComp 2.4) under Rocq 9.3 + MathComp 2.6, without editing
    classic sources.  It restores two Rocq 9.0 defaults that changed in 9.3:
    1. ssreflect `rewrite` generates side conditions after the main goal;
    2. `intuition` falls back to `auto with *` (9.0 definition of
       Tauto.intuition_solver, without its deprecation warning). *)
From mathcomp Require Import ssreflect.
#[export] Set SsrOldRewriteGoalsOrder.
Ltac Tauto.intuition_solver ::= first [ solve [auto] | solve [auto with *] | idtac ].
