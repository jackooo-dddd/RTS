From mathcomp Require Import ssreflect ssrbool eqtype.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTactics.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation.

Inductive EqValidationTrue : SProp := eq_validation_I.
Inductive EqValidationFalse : SProp := .

Definition eq_false_elim (P : SProp) (H : EqValidationFalse) : P :=
  match H return P with end.

Definition TacticsBoolRel (bR : bool) (bL : ImportedTactics.Bool) : SProp :=
  match bR, bL with
  | true, ImportedTactics.Bool_true => EqValidationTrue
  | false, ImportedTactics.Bool_false => EqValidationTrue
  | _, _ => EqValidationFalse
  end.

Definition coq_false_to_tactics_false
    (H : Logic.False) : ImportedTactics.False := match H return ImportedTactics.False with end.

Definition tactics_false_elim (P : SProp)
    (H : ImportedTactics.False) : P := match H return P with end.

(** Canonical realization of the approved representation change
    [eqType] -> carrier [Type] plus imported Lean [DecidableEq]. *)
Definition eqtype_to_tactics_decidable_eq (T : eqType) :
    ImportedTactics.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => ImportedTactics.Decidable_isTrue (Lean.eq x y)
        (coq_eq_to_imported_eq x y H)
    | ReflectF H => ImportedTactics.Decidable_isFalse (Lean.eq x y)
        (fun HL => coq_false_to_tactics_false
          (H (imported_eq_to_coq_eq x y HL)))
    end.

Lemma eqtype_equality_observation_certificate (T : eqType) (x y : T) :
  TacticsBoolRel (x == y)
    (ImportedTactics.Decidable_decide (Lean.eq x y)
      (eqtype_to_tactics_decidable_eq T x y)).
Proof.
  unfold eqtype_to_tactics_decidable_eq.
  destruct (@eqP T x y); cbn; exact eq_validation_I.
Qed.

Lemma eqtype_disequality_observation_certificate (T : eqType) (x y : T) :
  TacticsBoolRel (x != y)
    (ImportedTactics.Decidable_decide (ImportedTactics.Ne T x y)
      (ImportedTactics.instDecidableNot (Lean.eq x y)
        (eqtype_to_tactics_decidable_eq T x y))).
Proof.
  unfold eqtype_to_tactics_decidable_eq.
  destruct (@eqP T x y); cbn; exact eq_validation_I.
Qed.

Print Assumptions eqtype_equality_observation_certificate.
Print Assumptions eqtype_disequality_observation_certificate.
