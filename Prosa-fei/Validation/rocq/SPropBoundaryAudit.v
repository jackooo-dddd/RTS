From LeanImport Require Import Lean.
Require Import ImportedEasy93 ProcessorStateBridge.

(** Empty [SProp] can eliminate into [Prop]; the actual boundary concerns
    non-singleton witness-carrying propositions below. *)
Definition imported_sfalse_to_rocq_false
    (H : Validation_SFalse) : False :=
  match H return False with end.

(** Conversely, Rocq rejects elimination of an ordinary [Prop] existential
    into imported Lean [SProp], even when a pointwise mapper is supplied. *)
Fail Definition rocq_exists_to_imported_exists
    (A : Type) (P : A -> Prop) (Q : A -> SProp)
    (map_witness : forall x, P x -> Q x)
    (H : exists x, P x) : Exists A Q :=
  match H with
  | ex_intro _ x Hx => Exists_intro A Q x (map_witness x Hx)
  end.

Fail Definition imported_exists_to_rocq_exists
    (A : Type) (P : A -> SProp) (Q : A -> Prop)
    (map_witness : forall x, P x -> Q x)
    (H : Exists A P) : exists x, Q x :=
  match H with
  | Exists_intro _ _ x Hx => ex_intro Q x (map_witness x Hx)
  end.
