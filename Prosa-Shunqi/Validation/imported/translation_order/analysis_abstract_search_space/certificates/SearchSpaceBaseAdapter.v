From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSearchSpace.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.

(** All relations below are about actual imported constructors and operations.
    They are input relations, not axioms or unproved semantic premises. *)

Definition ss_decidable_eq (T : eqType) : ImportedSearchSpace.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => ImportedSearchSpace.Decidable_isTrue (Lean.eq x y)
        (coq_eq_to_imported_eq x y H)
    | ReflectF H => ImportedSearchSpace.Decidable_isFalse (Lean.eq x y)
        (fun HL => match H (imported_eq_to_coq_eq x y HL) with end)
    end.

Definition SearchFunRel (T : Type) (fR : nat -> T) (fL : Lean.Nat -> T) : SProp :=
  forall xR xL, SubNatRel xR xL -> Lean.eq (fR xR) (fL xL).

Definition SearchIBFRel (fR : nat -> nat -> nat)
    (fL : Lean.Nat -> Lean.Nat -> Lean.Nat) : SProp :=
  forall aR aL xR xL,
    SubNatRel aR aL -> SubNatRel xR xL ->
    SubNatRel (fR aR xR) (fL aL xL).

Definition ss_target_one : Lean.Nat :=
  ImportedSearchSpace.OfNat_ofNat_inst1 Lean.Nat 1
    (ImportedSearchSpace.instOfNatNat 1).

Definition ss_target_sub (a b : Lean.Nat) : Lean.Nat :=
  ImportedSearchSpace.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedSearchSpace.instHSub_inst1 Lean.Nat ImportedSearchSpace.instSubNat)
    a b.

Lemma ss_target_one_canonical : SubNatRel 1 ss_target_one.
Proof. exact (@Lean.eq_refl Lean.Nat (Lean.Nat_succ Lean.Nat_zero)). Qed.

Lemma ss_target_sub_one_canonical (a : nat) :
  SubNatRel (a - 1) (ss_target_sub (sub_nat_to_imported a) ss_target_one).
Proof.
  destruct a as [|a].
  - change (Lean.eq Lean.Nat_zero Lean.Nat_zero).
    exact (@Lean.eq_refl Lean.Nat Lean.Nat_zero).
  - rewrite subn1.
    change (Lean.eq (sub_nat_to_imported a) (sub_nat_to_imported a)).
    exact (@Lean.eq_refl Lean.Nat (sub_nat_to_imported a)).
Qed.

Lemma ss_target_sub_one_related aR aL :
  SubNatRel aR aL ->
  SubNatRel (aR - 1) (ss_target_sub aL ss_target_one).
Proof.
  intro Ha. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (ss_target_sub_one_canonical aR)
    (sub_imported_eq_congr (fun z => ss_target_sub z ss_target_one)
      _ _ Ha)).
Qed.

Print Assumptions ss_decidable_eq.
Print Assumptions ss_target_sub_one_related.
