(** Auditable logical foundation between Rocq [Prop] and the [SProp] used by
    rocq-lean-import for Lean propositions.

    Kernel-proved forward operations are definitions in this file.  The only
    sole axiom is the sort-crossing principle that cannot be expressed by
    Rocq's elimination rules: interpreting strict truth back in [Prop]. *)

From LeanImport Require Import Lean.

Variant StrictlyInhabited (P : Prop) : SProp :=
| strictly_inhabits : P -> StrictlyInhabited P.

Arguments strictly_inhabits {P} _.

Definition embed_prop (P : Prop) : P -> StrictlyInhabited P :=
  fun p => strictly_inhabits p.

(** AXIOMATIC CORE 1/1: Rocq forbids eliminating an arbitrary [SProp]
    inhabitant into [Prop]. *)
Axiom interpret_strict :
  forall P : Prop, StrictlyInhabited P -> P.

Variant StrictlyExists (A : Type) (P : A -> Prop) : SProp :=
| strictly_exists : forall x : A, P x -> StrictlyExists A P.

Arguments strictly_exists {A P} _ _.

(** Kernel-proved in Rocq 9.3: [Prop] existential elimination into this
    proof-irrelevant [SProp] witness package is accepted. *)
Definition embed_exists :
  forall (A : Type) (P : A -> Prop),
    (exists x, P x) -> StrictlyExists A P :=
  fun A P H =>
    match H with
    | ex_intro _ x px => strictly_exists x px
    end.

(** Kernel-proved: equality is a singleton proposition whose eliminator may
    construct the imported Lean equality in [SProp]. *)
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

Definition imported_eq_to_strict_eq {A : Type} (x y : A) (H : eq x y) :
    StrictlyInhabited (Logic.eq x y) :=
  match H in eq _ z return StrictlyInhabited (Logic.eq x z) with
  | eq_refl _ => strictly_inhabits (Logic.eq_refl x)
  end.

Record PropSPropRel (P : Prop) (Q : SProp) : Prop := {
  prop_to_sprop : P -> Q;
  sprop_to_prop : Q -> P
}.

Definition prop_sprop_rel_intro (P : Prop) (Q : SProp)
    (toQ : P -> Q) (toStrictP : Q -> StrictlyInhabited P) :
    PropSPropRel P Q :=
  {| prop_to_sprop := toQ;
     sprop_to_prop := fun q => interpret_strict P (toStrictP q) |}.

Print Assumptions embed_prop.
Print Assumptions coq_eq_to_imported_eq.
Print Assumptions imported_eq_to_coq_eq.
Print Assumptions imported_eq_to_strict_eq.
Print Assumptions interpret_strict.
Print Assumptions embed_exists.
Print Assumptions prop_sprop_rel_intro.
