(** Isolated theorem-level trust boundary between Rocq [Prop] and the [SProp]
    used by rocq-lean-import for Lean propositions.

    This is the minimal fragment of the lf-lean approach required here:
    [StrictlyInhabited P] embeds the truth of [P] in [SProp], while the single
    axiom below permits elimination back into [Prop]. *)

From LeanImport Require Import Lean.

Variant StrictlyInhabited (P : Prop) : SProp :=
| strictly_inhabits : P -> StrictlyInhabited P.

Arguments strictly_inhabits {P} _.

(** TRUST BOUNDARY. Every theorem using it must carry the dedicated status
    [CERTIFIED_WITH_PROP_SPROP_BRIDGE]. *)
Axiom prop_sprop_trusted_elim :
  forall P : Prop, StrictlyInhabited P -> P.

(** TRUST BOUNDARY for witness-carrying propositions.  Rocq deliberately
    forbids eliminating a [Prop] existential into [SProp], while Lean's
    [Exists] is imported into [SProp].  This bridge exposes exactly the
    missing witness transfer and nothing about a target proposition. *)
Variant StrictlyExists (A : Type) (P : A -> Prop) : SProp :=
| strictly_exists : forall x : A, P x -> StrictlyExists A P.

Arguments strictly_exists {A P} _ _.

Axiom prop_sprop_trusted_exists_intro :
  forall (A : Type) (P : A -> Prop),
    (exists x, P x) -> StrictlyExists A P.

(** TRUST BOUNDARY for equality-valued semantic bridges.  The importer maps
    Lean propositions, including Lean equality, to [SProp].  Rocq's native
    arithmetic and MathComp rewriting lemmas prove [Logic.eq] in [Prop].
    This declaration performs only that universe crossing; it does not assert
    any target-specific equality. *)
Axiom prop_sprop_trusted_eq_intro :
  forall (A : Type) (x y : A), Logic.eq x y -> eq x y.

Definition sprop_eq_to_strict_eq {A : Type} (x y : A) (H : eq x y) :
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
     sprop_to_prop := fun q => prop_sprop_trusted_elim P (toStrictP q) |}.

Print Assumptions prop_sprop_rel_intro.
Print Assumptions prop_sprop_trusted_exists_intro.
Print Assumptions prop_sprop_trusted_eq_intro.
