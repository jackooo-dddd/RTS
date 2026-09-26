(* Re-bound copy of the accepted readiness/basic JitterSvcIntervalOperations.v for the
   jitter projection artifact; only module names differ. *)
(** GENERATED ARTIFACT-LOCAL INSTANTIATION.
    source: Validation/certificates/behavior_service/ServiceIntervalOperations.v
    source-sha256: 21a10cfcecbaa693524609e432c756a15734f8f07ab168bf685de5298cd936e9
    imported-artifact-sha256: e34025aae0f77959dc58e20663acf5f7abdd5af7df286b3f30e38debcd065838 *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  bigop.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedReadinessJitterProjection ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence JitterSvcBaseAdapter
  JitterSvcNatBoolOperations.

(** Reusable half-open interval-sum correspondence for the exact list normal
form guarded by [ServiceComputationInterface]. *)

Fixpoint svc_nat_list_to_imported (xs : seq nat) :
    ImportedReadinessJitterProjection.List_inst1 Lean.Nat :=
  match xs with
  | [::] => ImportedReadinessJitterProjection.List_nil_inst1 Lean.Nat
  | x :: tail => ImportedReadinessJitterProjection.List_cons_inst1 Lean.Nat
      (sub_nat_to_imported x) (svc_nat_list_to_imported tail)
  end.

Definition SvcNatListRel (xsR : seq nat)
    (xsL : ImportedReadinessJitterProjection.List_inst1 Lean.Nat) : SProp :=
  Lean.eq (svc_nat_list_to_imported xsR) xsL.

Definition svc_target_list_fold_sum
    (xs : ImportedReadinessJitterProjection.List_inst1 Lean.Nat) : Lean.Nat :=
  ImportedReadinessJitterProjection.List_foldr_inst3 Lean.Nat Lean.Nat Lean.Nat_add
    svc_target_zero xs.

Definition SvcNatFunRel (fR : nat -> nat)
    (fL : Lean.Nat -> Lean.Nat) : SProp :=
  forall nR nL, SubNatRel nR nL -> SubNatRel (fR nR) (fL nL).

Lemma svc_target_range_succ (start len step : Lean.Nat) :
  Logic.eq
    (ImportedReadinessJitterProjection.List_range' start (Lean.Nat_succ len) step)
    (ImportedReadinessJitterProjection.List_cons_inst1 Lean.Nat start
      (ImportedReadinessJitterProjection.List_range'
        (Lean.Nat_add start step) len step)).
Proof. reflexivity. Qed.

Lemma svc_target_range_iota (start len : nat) :
  Logic.eq
    (ImportedReadinessJitterProjection.List_range'
      (sub_nat_to_imported start) (sub_nat_to_imported len) svc_target_one)
    (svc_nat_list_to_imported (iota start len)).
Proof.
  elim: len start => [|len IH] start.
  - reflexivity.
  - cbn [sub_nat_to_imported iota svc_nat_list_to_imported].
    rewrite svc_target_range_succ.
    have Hstart : Logic.eq
        (Lean.Nat_add (sub_nat_to_imported start) svc_target_one)
        (sub_nat_to_imported start.+1) by reflexivity.
    rewrite Hstart (IH start.+1). reflexivity.
Qed.

Lemma svc_range_related (startR lenR : nat)
    (startL lenL : Lean.Nat) :
  SubNatRel startR startL -> SubNatRel lenR lenL ->
  SvcNatListRel (iota startR lenR)
    (ImportedReadinessJitterProjection.List_range' startL lenL svc_target_one).
Proof.
  intros Hstart Hlen. unfold SvcNatListRel.
  exact (sub_imported_eq_trans _ _ _
    (coq_eq_to_imported_eq _ _
      (Logic.eq_sym (svc_target_range_iota startR lenR)))
    (sub_imported_eq_congr2
      (fun start len => ImportedReadinessJitterProjection.List_range'
        start len svc_target_one) _ _ _ _ Hstart Hlen)).
Qed.

Fixpoint svc_map_related_canonical
    (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat)
    (Hf : SvcNatFunRel fR fL) (xs : seq nat) :
  Lean.eq (svc_nat_list_to_imported (map fR xs))
    (ImportedReadinessJitterProjection.List_map_inst3 Lean.Nat Lean.Nat fL
      (svc_nat_list_to_imported xs)) :=
  match xs with
  | [::] => @Lean.eq_refl _ _
  | x :: tail => sub_imported_eq_congr2
      (ImportedReadinessJitterProjection.List_cons_inst1 Lean.Nat) _ _ _ _
      (Hf x (sub_nat_to_imported x) (sub_nat_rel_canonical x))
      (svc_map_related_canonical fR fL Hf tail)
  end.

Lemma svc_map_related
    (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat)
    (xsR : seq nat) (xsL : ImportedReadinessJitterProjection.List_inst1 Lean.Nat) :
  SvcNatFunRel fR fL -> SvcNatListRel xsR xsL ->
  SvcNatListRel (map fR xsR)
    (ImportedReadinessJitterProjection.List_map_inst3 Lean.Nat Lean.Nat fL xsL).
Proof.
  intros Hf Hxs. unfold SvcNatListRel in *.
  exact (sub_imported_eq_trans _ _ _
    (svc_map_related_canonical fR fL Hf xsR)
    (sub_imported_eq_congr
      (ImportedReadinessJitterProjection.List_map_inst3 Lean.Nat Lean.Nat fL) _ _ Hxs)).
Qed.

Fixpoint svc_fold_sum_canonical (xs : seq nat) :
  SubNatRel (foldr addn O xs)
    (svc_target_list_fold_sum (svc_nat_list_to_imported xs)).
Proof.
  destruct xs as [|x tail].
  - exact (sub_nat_rel_canonical O).
  - exact (svc_target_add_related x (sub_nat_to_imported x)
      (foldr addn O tail)
      (svc_target_list_fold_sum (svc_nat_list_to_imported tail))
      (sub_nat_rel_canonical x) (svc_fold_sum_canonical tail)).
Defined.

Lemma svc_fold_sum_related (xsR : seq nat)
    (xsL : ImportedReadinessJitterProjection.List_inst1 Lean.Nat) :
  SvcNatListRel xsR xsL ->
  SubNatRel (foldr addn O xsR) (svc_target_list_fold_sum xsL).
Proof.
  intro Hxs. unfold SvcNatListRel in Hxs.
  exact (sub_imported_eq_trans _ _ _ (svc_fold_sum_canonical xsR)
    (sub_imported_eq_congr svc_target_list_fold_sum _ _ Hxs)).
Qed.

Definition svc_target_interval_value
    (m n : Lean.Nat) (f : Lean.Nat -> Lean.Nat) : Lean.Nat :=
  svc_target_list_fold_sum
    (ImportedReadinessJitterProjection.List_map_inst3 Lean.Nat Lean.Nat f
      (ImportedReadinessJitterProjection.List_range' m (svc_target_sub n m)
        svc_target_one)).

Lemma svc_mathcomp_big_seq_as_fold (xs : seq nat) (f : nat -> nat) :
  Logic.eq (\sum_(i <- xs) f i) (foldr addn O (map f xs)).
Proof.
  elim: xs => [|x tail IH].
  - rewrite big_nil. reflexivity.
  - rewrite big_cons. cbn [map foldr]. now rewrite IH.
Qed.

Lemma svc_interval_sum_related
    (mR nR : nat) (mL nL : Lean.Nat)
    (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat) :
  SubNatRel mR mL -> SubNatRel nR nL -> SvcNatFunRel fR fL ->
  SubNatRel (\sum_(mR <= i < nR) fR i)
    (svc_target_interval_value mL nL fL).
Proof.
  intros Hm Hn Hf. unfold svc_target_interval_value.
  rewrite /index_iota svc_mathcomp_big_seq_as_fold.
  apply svc_fold_sum_related.
  apply svc_map_related; first exact Hf.
  exact (svc_range_related mR (nR - mR) mL
    (svc_target_sub nL mL) Hm
    (svc_target_sub_related nR nL mR mL Hn Hm)).
Qed.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN svc_interval_operations". exact I. Qed.
Print Assumptions svc_range_related.
Print Assumptions svc_fold_sum_related.
Print Assumptions svc_interval_sum_related.
Goal Logic.True.
Proof. idtac "AUDIT_END svc_interval_operations". exact I. Qed.
