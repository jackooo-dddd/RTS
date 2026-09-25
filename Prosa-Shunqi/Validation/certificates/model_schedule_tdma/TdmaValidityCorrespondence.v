From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import model.schedule.tdma.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTdmaProjectedFull.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  TdmaBaseAdapter TdmaSeqsetAdapter TdmaPolicyAdapter.

Lemma tdma_list_encoder_eq {T : Type} (xs : seq T) :
  Lean.eq (ar_list_to_imported xs) (seqset_seq_to_list xs).
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr
      (ImportedTdmaProjectedFull.List_cons T x) _ _ IH).
Qed.

Lemma tdma_set_list_related (Task : eqType)
    (tsR : @prosa.util.seqset.set Task)
    (tsL : ImportedTdmaProjectedFull.Prosa_Util_Seqset_set Task
      (ar_decidable_eq Task)) :
  RocqSeqSetRel Task tsR tsL ->
  ArListRel (@prosa.util.seqset._set_seq Task tsR)
    (ImportedTdmaProjectedFull.Prosa_Util_Seqset_set_val
      Task (ar_decidable_eq Task) tsL).
Proof.
  intro Hts.
  unfold RocqSeqSetRel in Hts.
  unfold ArListRel.
  exact (sub_imported_eq_trans _ _ _
    (tdma_list_encoder_eq _ ) Hts).
Qed.

Lemma tdma_and_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P /\ Q) (Lean.And PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [p q]. exact (Lean.And_intro PL QL
      (prop_to_sprop _ _ HP p) (prop_to_sprop _ _ HQ q)).
  - intro H. apply strictly_inhabits. split.
    + exact (sprop_to_prop _ _ HP
        (ImportedTdmaProjectedFull.And_left _ _ H)).
    + exact (sprop_to_prop _ _ HQ
        (ImportedTdmaProjectedFull.And_right _ _ H)).
Qed.

Section Validity.
  Context (Task : eqType).
  Context (policyR : prosa.model.schedule.tdma.TDMAPolicy Task).
  Context (policyL : ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_TDMAPolicy
    Task (ar_decidable_eq Task)).
  Context (Hpolicy : TdmaPolicyRel Task policyR policyL).

  Lemma tdma_order_truth x y :
    PropSPropRel
      (is_true (@prosa.model.schedule.tdma.slot_order Task policyR x y))
      (Lean.eq
        (ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_TDMAPolicy_slot_order
          Task (ar_decidable_eq Task) policyL x y)
        ImportedTdmaProjectedFull.Bool_true).
  Proof.
    exact (ar_bool_truth_correspondence _ _
      (tdma_order_related _ _ _ Hpolicy x y)).
  Qed.

  Lemma tdma_slot_positive_truth tsk :
    PropSPropRel
      (is_true (ltn O (@prosa.model.schedule.tdma.task_time_slot
        Task policyR tsk)))
      (ImportedTdmaProjectedFull.LT_lt_inst1 Lean.Nat
        ImportedTdmaProjectedFull.instLTNat
        Lean.Nat_zero
        (ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_TDMAPolicy_task_time_slot
          Task (ar_decidable_eq Task) policyL tsk)).
  Proof.
    change (PropSPropRel
      (is_true (ltn O (@prosa.model.schedule.tdma.task_time_slot
        Task policyR tsk)))
      (sub_imported_lt Lean.Nat_zero
        (ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_TDMAPolicy_task_time_slot
          Task (ar_decidable_eq Task) policyL tsk))).
    apply sub_nat_lt_correspondence.
    - exact (sub_nat_rel_canonical O).
    - exact (tdma_slot_related _ _ _ Hpolicy tsk).
  Qed.

  Theorem transitive_slot_order_correspondence :
    PropSPropRel
      (@prosa.model.schedule.tdma.transitive_slot_order Task policyR)
      (ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_transitive_slot_order
        Task (ar_decidable_eq Task) policyL).
  Proof.
    apply prop_sprop_rel_intro.
    - intros HR y x z Hxy Hyz.
      apply (prop_to_sprop _ _ (tdma_order_truth x z)).
      exact (HR y x z
        (sprop_to_prop _ _ (tdma_order_truth x y) Hxy)
        (sprop_to_prop _ _ (tdma_order_truth y z) Hyz)).
    - intro HL. apply strictly_inhabits.
      intros y x z Hxy Hyz.
      apply (sprop_to_prop _ _ (tdma_order_truth x z)).
      exact (HL y x z
        (prop_to_sprop _ _ (tdma_order_truth x y) Hxy)
        (prop_to_sprop _ _ (tdma_order_truth y z) Hyz)).
  Qed.

  Theorem total_slot_order_correspondence
      (tsR : @prosa.util.seqset.set Task)
      (tsL : ImportedTdmaProjectedFull.Prosa_Util_Seqset_set Task
        (ar_decidable_eq Task))
      (Hts : RocqSeqSetRel Task tsR tsL) :
    PropSPropRel
      (@prosa.model.schedule.tdma.total_slot_order Task tsR policyR)
      (ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_total_slot_order
        Task (ar_decidable_eq Task) policyL tsL).
  Proof.
    pose proof (tdma_set_list_related Task tsR tsL Hts) as Hlist.
    apply prop_sprop_rel_intro.
    - intros HR x y Hx Hy.
      have HxR := sprop_to_prop _ _
        (ar_membership_correspondence Task x _ _ Hlist) Hx.
      have HyR := sprop_to_prop _ _
        (ar_membership_correspondence Task y _ _ Hlist) Hy.
      destruct (HR x y HxR HyR) as [Hxy | Hyx].
      + exact (Lean.Or_inl _ _
          (prop_to_sprop _ _ (tdma_order_truth x y) Hxy)).
      + exact (Lean.Or_inr _ _
          (prop_to_sprop _ _ (tdma_order_truth y x) Hyx)).
    - intro HL. apply strictly_inhabits.
      intros x y HxR HyR.
      have HxL := prop_to_sprop _ _
        (ar_membership_correspondence Task x _ _ Hlist) HxR.
      have HyL := prop_to_sprop _ _
        (ar_membership_correspondence Task y _ _ Hlist) HyR.
      apply (interpret_strict _).
      destruct (HL x y HxL HyL) as [Hxy | Hyx].
      + exact (strictly_inhabits
          (or_introl _ (sprop_to_prop _ _ (tdma_order_truth x y) Hxy))).
      + exact (strictly_inhabits
          (or_intror _ (sprop_to_prop _ _ (tdma_order_truth y x) Hyx))).
  Qed.

  Theorem antisymmetric_slot_order_correspondence
      (tsR : @prosa.util.seqset.set Task)
      (tsL : ImportedTdmaProjectedFull.Prosa_Util_Seqset_set Task
        (ar_decidable_eq Task))
      (Hts : RocqSeqSetRel Task tsR tsL) :
    PropSPropRel
      (@prosa.model.schedule.tdma.antisymmetric_slot_order Task tsR policyR)
      (ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_antisymmetric_slot_order
        Task (ar_decidable_eq Task) policyL tsL).
  Proof.
    pose proof (tdma_set_list_related Task tsR tsL Hts) as Hlist.
    apply prop_sprop_rel_intro.
    - intros HR x y Hx Hy Hxy Hyx.
      apply coq_eq_to_imported_eq.
      apply HR.
      + exact (sprop_to_prop _ _
          (ar_membership_correspondence Task x _ _ Hlist) Hx).
      + exact (sprop_to_prop _ _
          (ar_membership_correspondence Task y _ _ Hlist) Hy).
      + exact (sprop_to_prop _ _ (tdma_order_truth x y) Hxy).
      + exact (sprop_to_prop _ _ (tdma_order_truth y x) Hyx).
    - intro HL. apply strictly_inhabits.
      intros x y Hx Hy Hxy Hyx.
      apply imported_eq_to_coq_eq.
      apply HL.
      + exact (prop_to_sprop _ _
          (ar_membership_correspondence Task x _ _ Hlist) Hx).
      + exact (prop_to_sprop _ _
          (ar_membership_correspondence Task y _ _ Hlist) Hy).
      + exact (prop_to_sprop _ _ (tdma_order_truth x y) Hxy).
      + exact (prop_to_sprop _ _ (tdma_order_truth y x) Hyx).
  Qed.

  Theorem valid_time_slot_correspondence
      (tsR : @prosa.util.seqset.set Task)
      (tsL : ImportedTdmaProjectedFull.Prosa_Util_Seqset_set Task
        (ar_decidable_eq Task))
      (Hts : RocqSeqSetRel Task tsR tsL) :
    PropSPropRel
      (@prosa.model.schedule.tdma.valid_time_slot Task tsR policyR)
      (ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_valid_time_slot
        Task (ar_decidable_eq Task) policyL tsL).
  Proof.
    pose proof (tdma_set_list_related Task tsR tsL Hts) as Hlist.
    apply prop_sprop_rel_intro.
    - intros HR tsk HmemL.
      apply (prop_to_sprop _ _ (tdma_slot_positive_truth tsk)).
      apply HR.
      exact (sprop_to_prop _ _
        (ar_membership_correspondence Task tsk _ _ Hlist) HmemL).
    - intro HL. apply strictly_inhabits.
      intros tsk HmemR.
      apply (sprop_to_prop _ _ (tdma_slot_positive_truth tsk)).
      apply HL.
      exact (prop_to_sprop _ _
        (ar_membership_correspondence Task tsk _ _ Hlist) HmemR).
  Qed.

  Theorem valid_TDMAPolicy_correspondence
      (tsR : @prosa.util.seqset.set Task)
      (tsL : ImportedTdmaProjectedFull.Prosa_Util_Seqset_set Task
        (ar_decidable_eq Task))
      (Hts : RocqSeqSetRel Task tsR tsL) :
    PropSPropRel
      (@prosa.model.schedule.tdma.valid_TDMAPolicy Task tsR policyR)
      (ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_valid_TDMAPolicy
        Task (ar_decidable_eq Task) policyL tsL).
  Proof.
    change (PropSPropRel
      (@prosa.model.schedule.tdma.transitive_slot_order Task policyR /\
       @prosa.model.schedule.tdma.total_slot_order Task tsR policyR /\
       @prosa.model.schedule.tdma.antisymmetric_slot_order Task tsR policyR /\
       @prosa.model.schedule.tdma.valid_time_slot Task tsR policyR)
      (Lean.And
        (ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_transitive_slot_order
          Task (ar_decidable_eq Task) policyL)
        (Lean.And
          (ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_total_slot_order
            Task (ar_decidable_eq Task) policyL tsL)
          (Lean.And
            (ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_antisymmetric_slot_order
              Task (ar_decidable_eq Task) policyL tsL)
            (ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_valid_time_slot
              Task (ar_decidable_eq Task) policyL tsL))))).
    apply tdma_and_correspondence.
    - exact transitive_slot_order_correspondence.
    - apply tdma_and_correspondence.
      + exact (total_slot_order_correspondence tsR tsL Hts).
      + apply tdma_and_correspondence.
        * exact (antisymmetric_slot_order_correspondence tsR tsL Hts).
        * exact (valid_time_slot_correspondence tsR tsL Hts).
  Qed.
End Validity.

Print Assumptions tdma_set_list_related.
Print Assumptions transitive_slot_order_correspondence.
Print Assumptions total_slot_order_correspondence.
Print Assumptions antisymmetric_slot_order_correspondence.
Print Assumptions valid_time_slot_correspondence.
Print Assumptions valid_TDMAPolicy_correspondence.
