From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsTdmaSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsTdma ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  FtdmaBaseAdapter FtdmaArithmeticAdapter FtdmaSeqsetAdapter FtdmaPolicyAdapter
  FtdmaValidityCorrespondence FtdmaNumericCorrespondence.

Module I := ImportedFactsTdma.
Module S := FactsTdmaSemanticSource.FactsTdmaSemanticSource.

(** Statement correspondences for [analysis/facts/tdma.v].

    Source side: the extracted statement [S.statement_X] (whose printed body is
    checked equal to the authoritative elaborated type) specialised at the
    leading input binders [Task], [ts], [TDMAPolicy].  Target side: the type
    of the imported Lean theorem [I.Prosa_Analysis_Facts_Tdma_X] at the related
    inputs.  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma ft_imp (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P -> Q) (PL -> QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros H p. apply (prop_to_sprop _ _ HQ). exact (H (sprop_to_prop _ _ HP p)).
  - intro H. apply strictly_inhabits. intro p.
    apply (sprop_to_prop _ _ HQ). exact (H (prop_to_sprop _ _ HP p)).
Qed.

Lemma ft_forall_id (T : Type) (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (forall x, PR x) (forall x, PL x).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros HR x. exact (prop_to_sprop _ _ (HP x) (HR x)).
  - intro HL. apply strictly_inhabits. intro x. exact (sprop_to_prop _ _ (HP x) (HL x)).
Qed.

Lemma ft_forall_nat (PR : nat -> Prop) (PL : Lean.Nat -> SProp) :
  (forall nR nL, SubNatRel nR nL -> PropSPropRel (PR nR) (PL nL)) ->
  PropSPropRel (forall nR, PR nR) (forall nL, PL nL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros HR nL. exact (prop_to_sprop _ _
      (HP (sub_nat_to_rocq nL) nL (sub_nat_rel_surjective nL)) (HR (sub_nat_to_rocq nL))).
  - intro HL. apply strictly_inhabits. intro nR.
    exact (sprop_to_prop _ _
      (HP nR (sub_nat_to_imported nR) (sub_nat_rel_canonical nR)) (HL (sub_nat_to_imported nR))).
Qed.

Lemma ft_eq (T : Type) (x y : T) : PropSPropRel (x = y) (Lean.eq x y).
Proof.
  apply prop_sprop_rel_intro.
  - exact (coq_eq_to_imported_eq x y).
  - intro H. apply strictly_inhabits. exact (imported_eq_to_coq_eq x y H).
Qed.

Section FactsTdma.
  Context (Task : eqType).
  Let d := ar_decidable_eq Task.
  Variable policyR : prosa.model.schedule.tdma.TDMAPolicy Task.
  Variable policyL : I.Prosa_Model_Schedule_Tdma_TDMAPolicy Task d.
  Hypothesis Hpolicy : TdmaPolicyRel Task policyR policyL.
  Variable tsR : @prosa.util.seqset.set Task.
  Variable tsL : I.Prosa_Util_Seqset_set Task d.
  Hypothesis Hts : RocqSeqSetRel Task tsR tsL.

  Let CYCLE := TDMA_cycle_correspondence Task policyR policyL Hpolicy tsR tsL Hts.
  Let OFFSET := task_slot_offset_correspondence Task policyR policyL Hpolicy tsR tsL Hts.
  Let SLOT := tdma_slot_related _ _ _ Hpolicy.

  Lemma ft_mem (x : Task) :
    PropSPropRel (x \in tsR)
      (I.Membership_mem Task (I.Prosa_Util_Seqset_set Task d)
        (I.Prosa_Util_Seqset_instMembershipSet Task d) tsL x).
  Proof. exact (ar_membership_correspondence Task x _ _ (tdma_set_list_related Task tsR tsL Hts)). Qed.

  Let VALID := valid_time_slot_correspondence Task policyR policyL Hpolicy tsR tsL Hts.
  Let TOTAL := total_slot_order_correspondence Task policyR policyL Hpolicy tsR tsL Hts.
  Let ANTI := antisymmetric_slot_order_correspondence Task policyR policyL Hpolicy tsR tsL Hts.
  Let TRANS := transitive_slot_order_correspondence Task policyR policyL Hpolicy.

  Definition src_TDMA_cycle_ge_each_time_slot : Prop :=
    ltac:(body_of (fun s : S.statement_TDMA_cycle_ge_each_time_slot => s Task tsR policyR)).
  Definition tgt_TDMA_cycle_ge_each_time_slot : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Tdma_TDMA_cycle_ge_each_time_slot Task d tsL policyL)).
  Theorem TDMA_cycle_ge_each_time_slot_correspondence :
    PropSPropRel src_TDMA_cycle_ge_each_time_slot tgt_TDMA_cycle_ge_each_time_slot.
  Proof.
    apply ft_forall_id => task.
    apply ft_imp; [exact (ft_mem task)|].
    exact (sub_nat_le_correspondence _ _ _ _ (SLOT task) CYCLE).
  Qed.

  Definition src_TDMA_cycle_positive : Prop :=
    ltac:(body_of (fun s : S.statement_TDMA_cycle_positive => s Task tsR policyR)).
  Definition tgt_TDMA_cycle_positive : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Tdma_TDMA_cycle_positive Task d tsL policyL)).
  Theorem TDMA_cycle_positive_correspondence :
    PropSPropRel src_TDMA_cycle_positive tgt_TDMA_cycle_positive.
  Proof.
    apply ft_forall_id => task.
    apply ft_imp; [exact (ft_mem task)|].
    apply ft_imp; [exact VALID|].
    exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) CYCLE).
  Qed.

  Definition src_Offset_lt_cycle : Prop :=
    ltac:(body_of (fun s : S.statement_Offset_lt_cycle => s Task tsR policyR)).
  Definition tgt_Offset_lt_cycle : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Tdma_Offset_lt_cycle Task d tsL policyL)).
  Theorem Offset_lt_cycle_correspondence :
    PropSPropRel src_Offset_lt_cycle tgt_Offset_lt_cycle.
  Proof.
    apply ft_forall_id => task.
    apply ft_imp; [exact (ft_mem task)|].
    apply ft_imp; [exact VALID|].
    exact (sub_nat_lt_correspondence _ _ _ _ (OFFSET task) CYCLE).
  Qed.

  Definition src_Offset_add_slot_leq_cycle : Prop :=
    ltac:(body_of (fun s : S.statement_Offset_add_slot_leq_cycle => s Task tsR policyR)).
  Definition tgt_Offset_add_slot_leq_cycle : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Tdma_Offset_add_slot_leq_cycle Task d tsL policyL)).
  Theorem Offset_add_slot_leq_cycle_correspondence :
    PropSPropRel src_Offset_add_slot_leq_cycle tgt_Offset_add_slot_leq_cycle.
  Proof.
    apply ft_forall_id => task.
    apply ft_imp; [exact (ft_mem task)|].
    exact (sub_nat_le_correspondence _ _ _ _
      (tdma_nat_add_related _ _ _ _ (OFFSET task) (SLOT task)) CYCLE).
  Qed.

  Definition src_relation_offset : Prop :=
    ltac:(body_of (fun s : S.statement_relation_offset => s Task tsR policyR)).
  Definition tgt_relation_offset : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Tdma_relation_offset Task d tsL policyL)).
  Theorem relation_offset_correspondence :
    PropSPropRel src_relation_offset tgt_relation_offset.
  Proof.
    apply ft_imp; [exact ANTI|].
    apply ft_imp; [exact TRANS|].
    apply ft_forall_id => tsk1.
    apply ft_forall_id => tsk2.
    apply ft_imp; [exact (ft_mem tsk1)|].
    apply ft_imp; [exact (ft_mem tsk2)|].
    apply ft_imp; [exact (tdma_order_truth Task policyR policyL Hpolicy tsk1 tsk2)|].
    apply ft_imp; [exact (ar_bool_truth_correspondence _ _ (tdma_ne_observation Task tsk1 tsk2))|].
    exact (sub_nat_le_correspondence _ _ _ _
      (tdma_nat_add_related _ _ _ _ (OFFSET tsk1) (SLOT tsk1)) (OFFSET tsk2)).
  Qed.

  Definition src_task_in_time_slot_uniq : Prop :=
    ltac:(body_of (fun s : S.statement_task_in_time_slot_uniq => s Task tsR policyR)).
  Definition tgt_task_in_time_slot_uniq : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Tdma_task_in_time_slot_uniq Task d tsL policyL)).
  Theorem task_in_time_slot_uniq_correspondence :
    PropSPropRel src_task_in_time_slot_uniq tgt_task_in_time_slot_uniq.
  Proof.
    apply ft_forall_id => task.
    apply ft_imp; [exact (ft_mem task)|].
    apply ft_imp; [exact VALID|].
    apply ft_imp; [exact TOTAL|].
    apply ft_imp; [exact ANTI|].
    apply ft_imp; [exact TRANS|].
    apply ft_forall_id => tsk1.
    apply ft_forall_id => tsk2.
    apply ft_forall_nat => tR tL Ht.
    apply ft_imp; [exact (ft_mem tsk1)|].
    apply ft_imp; [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (SLOT tsk1))|].
    apply ft_imp; [exact (ft_mem tsk2)|].
    apply ft_imp; [exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (SLOT tsk2))|].
    apply ft_imp; [exact (ar_bool_truth_correspondence _ _
      (task_in_time_slot_correspondence Task policyR policyL Hpolicy tsR tsL Hts tsk1 tR tL Ht))|].
    apply ft_imp; [exact (ar_bool_truth_correspondence _ _
      (task_in_time_slot_correspondence Task policyR policyL Hpolicy tsR tsL Hts tsk2 tR tL Ht))|].
    exact (ft_eq Task tsk1 tsk2).
  Qed.
End FactsTdma.
