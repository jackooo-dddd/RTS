(** Audited logical foundation for Lean propositions imported as Rocq SProp. *)
From LeanImport Require Import Lean.

Variant StrictlyInhabited (P : Prop) : SProp :=
| strictly_inhabits : P -> StrictlyInhabited P.

Arguments strictly_inhabits {P} _.

Definition embed_prop (P : Prop) : P -> StrictlyInhabited P :=
  fun p => strictly_inhabits p.

(** The sole axiomatic component: Rocq forbids eliminating arbitrary SProp
    evidence into Prop. *)
Axiom interpret_strict :
  forall P : Prop, StrictlyInhabited P -> P.

Definition coq_eq_to_imported_eq {A : Type} (x y : A) :
    Logic.eq x y -> eq x y :=
  fun H => match H in Logic.eq _ z return eq x z with
           | Logic.eq_refl => eq_refl x
           end.

Definition imported_eq_to_coq_eq {A : Type} (x y : A) :
    eq x y -> Logic.eq x y :=
  fun H => match H in eq _ z return Logic.eq x z with
           | eq_refl _ => Logic.eq_refl x
           end.

Record PropSPropRel (P : Prop) (Q : SProp) : Prop := {
  prop_to_sprop : P -> Q;
  sprop_to_prop : Q -> P
}.

