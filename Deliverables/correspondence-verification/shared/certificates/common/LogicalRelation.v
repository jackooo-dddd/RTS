From LeanImport Require Import Lean.
From FoundationCertificates Require Import PropSPropFoundation.

(** Relation used for source reflection views and other informative singleton
    families that live in [Set], rather than [Prop].  No sort-crossing axiom is
    needed when the backward map constructs the source view without
    eliminating its SProp argument. *)
Record SetSPropRel (A : Set) (Q : SProp) : Prop := {
  set_to_sprop : A -> Q;
  sprop_to_set : Q -> A
}.

(** Reusable theorem-level combinator.  The forward direction is kernel
    proved; only the backward SProp-to-Prop interpretation reaches the sole
    audited foundation axiom [interpret_strict]. *)
Definition prop_sprop_rel_intro (P : Prop) (Q : SProp)
    (toQ : P -> Q) (toStrictP : Q -> StrictlyInhabited P) :
    PropSPropRel P Q :=
  {| prop_to_sprop := toQ;
     sprop_to_prop := fun q => interpret_strict P (toStrictP q) |}.

Definition imported_eq_to_strict_eq {A : Type} (x y : A)
    (H : Lean.eq x y) : StrictlyInhabited (Logic.eq x y) :=
  match H in Lean.eq _ z return StrictlyInhabited (Logic.eq x z) with
  | eq_refl _ => strictly_inhabits (Logic.eq_refl x)
  end.

Print Assumptions prop_sprop_rel_intro.
Print Assumptions imported_eq_to_strict_eq.
