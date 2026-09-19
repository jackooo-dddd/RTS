From LeanImport Require Import Lean.
Require Import PropSPropFoundation.

(** Positive kernel probe: Rocq 9.3 accepts this elimination into [SProp]. *)
Definition direct_prop_exists_to_strict_exists
    (A : Type) (P : A -> Prop) (H : exists x, P x) : StrictlyExists A P :=
  match H with
  | ex_intro _ x px => strictly_exists x px
  end.
