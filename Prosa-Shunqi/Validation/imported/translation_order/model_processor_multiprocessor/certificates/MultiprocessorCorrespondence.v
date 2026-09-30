From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import behavior.all model.processor.multiprocessor.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedMultiprocessor ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations.

Module I := ImportedMultiprocessor.

(** Correspondences for [model/processor/multiprocessor.v].

    Inputs.  Jobs are an identity carrier.  The per-core processor models are
    related by the accepted two-sided [SvcProcessorStateRel] together with the
    per-core supply relation [Hsupply_on] (the record relates scheduling and
    service; supply is related separately, as in the restricted-supply
    family).  Processor counts are related by [SubNatRel]; an ordinal
    ['I_nR] and a Lean [Fin nL] are related when their values are
    ([MpOrdRel]); multiprocessor states are related pointwise over related
    processors ([MpStateRel]).  Both carriers have two-way totals.

    The finite sum over [Fin n] (the core sum of the multiprocessor instance
    and the right-hand side of [multiproc_service_in_eq]) is related through
    the exported, kernel-checked Lean equation
    [MultiprocessorInterface.production_fin_sum] (a propositional equation
    used by transport, not a definitional unfolding) and the accepted
    half-open interval-sum relation [svc_interval_sum_related]. *)

Definition mp_target_lt (a b : Lean.Nat) : SProp :=
  I.LT_lt_inst1 Lean.Nat I.instLTNat a b.

Lemma mp_nat_lt_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (ltn aR bR)) (mp_target_lt aL bL).
Proof.
  intros Ha Hb. unfold mp_target_lt.
  exact (sub_nat_lt_correspondence aR aL bR bL Ha Hb).
Qed.

Lemma mp_nat_input (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
Qed.

Definition mp_target_false_elim (Q : SProp) (H : I.False) : Q :=
  match H return Q with end.

(** * Processors: ordinals and [Fin] values *)

Definition MpOrdRel (nR : nat) (nL : Lean.Nat) (oR : 'I_nR) (oL : Fin nL) : SProp :=
  SubNatRel (nat_of_ord oR) (I.Fin_val nL oL).

Definition mp_ord_to_fin (nR : nat) (nL : Lean.Nat) (Hn : SubNatRel nR nL)
    (oR : 'I_nR) : Fin nL :=
  Fin_mk nL (sub_nat_to_imported (nat_of_ord oR))
    (prop_to_sprop _ _
      (mp_nat_lt_correspondence (nat_of_ord oR) _ nR nL (sub_nat_rel_canonical _) Hn)
      (ltn_ord oR)).

Definition mp_fin_to_ord (nR : nat) (nL : Lean.Nat) (Hn : SubNatRel nR nL)
    (oL : Fin nL) : 'I_nR :=
  @Ordinal nR (sub_nat_to_rocq (I.Fin_val nL oL))
    (sprop_to_prop _ _
      (mp_nat_lt_correspondence _ (I.Fin_val nL oL) nR nL
        (sub_nat_rel_surjective (I.Fin_val nL oL)) Hn)
      (I.Fin_isLt nL oL)).

Lemma mp_ord_rel_canonical nR nL (Hn : SubNatRel nR nL) (oR : 'I_nR) :
  MpOrdRel nR nL oR (mp_ord_to_fin nR nL Hn oR).
Proof. exact (sub_nat_rel_canonical _). Qed.

Lemma mp_ord_rel_surjective nR nL (Hn : SubNatRel nR nL) (oL : Fin nL) :
  MpOrdRel nR nL (mp_fin_to_ord nR nL Hn oL) oL.
Proof. exact (sub_nat_rel_surjective _). Qed.

(** Related ordinals are determined by the Lean value, and conversely. *)
Lemma mp_ord_rel_source_unique nR nL (Hn : SubNatRel nR nL) (oR : 'I_nR) (oL : Fin nL) :
  MpOrdRel nR nL oR oL -> Logic.eq (mp_fin_to_ord nR nL Hn oL) oR.
Proof.
  intro H. apply: val_inj. cbn. exact (mp_nat_input _ _ H).
Qed.

Lemma mp_ord_rel_target_unique nR nL (Hn : SubNatRel nR nL) (oR : 'I_nR) (oL : Fin nL) :
  MpOrdRel nR nL oR oL -> Lean.eq (mp_ord_to_fin nR nL Hn oR) oL.
Proof.
  destruct oL as [v h]. unfold MpOrdRel, SubNatRel. cbn.
  intro H. unfold mp_ord_to_fin.
  destruct H. exact (@Lean.eq_refl _ _).
Qed.

Theorem processor_source_total nR nL (Hn : SubNatRel nR nL) (oR : 'I_nR) :
  MpOrdRel nR nL oR (mp_ord_to_fin nR nL Hn oR).
Proof. exact (mp_ord_rel_canonical nR nL Hn oR). Qed.

Theorem processor_target_total nR nL (Hn : SubNatRel nR nL)
    (oL : I.Prosa_Model_Processor_Multiprocessor_processor nL) :
  MpOrdRel nR nL
    (mp_fin_to_ord nR nL Hn oL : prosa.model.processor.multiprocessor.processor nR) oL.
Proof. exact (mp_ord_rel_surjective nR nL Hn oL). Qed.

(** * The finite sum over [Fin n] *)

Definition mp_source_ord_family (nR : nat) (FR : 'I_nR -> nat) (k : nat) : nat :=
  if insub k is Some o then FR o else O.

Lemma mp_source_ord_sum_as_interval (nR : nat) (FR : 'I_nR -> nat) :
  Logic.eq (\sum_(i < nR) FR i) (\sum_(0 <= k < nR) mp_source_ord_family nR FR k).
Proof.
  rewrite big_mkord. apply: eq_bigr => i _. unfold mp_source_ord_family.
  rewrite valK. reflexivity.
Qed.

Definition mp_target_ord_family (nL : Lean.Nat) (fL : Fin nL -> Lean.Nat) (k : Lean.Nat) : Lean.Nat :=
  I.dite Lean.Nat (I.LT_lt_inst1 Lean.Nat I.instLTNat k nL) (I.Nat_decLt k nL)
    (fun h => fL (Fin_mk nL k h))
    (fun _ => I.OfNat_ofNat_inst1 Lean.Nat Lean.Nat_zero (I.instOfNatNat Lean.Nat_zero)).

Section FinSum.
  Variables (nR : nat) (nL : Lean.Nat).
  Hypothesis Hn : SubNatRel nR nL.
  Variable FR : 'I_nR -> nat.
  Variable fL : Fin nL -> Lean.Nat.
  Hypothesis Hf : forall oR oL, MpOrdRel nR nL oR oL -> SubNatRel (FR oR) (fL oL).

  Lemma mp_source_ord_family_lt (k : nat) (Hk : is_true (ltn k nR)) :
    Logic.eq (mp_source_ord_family nR FR k) (FR (Ordinal Hk)).
  Proof. unfold mp_source_ord_family. rewrite (insubT (fun x => ltn x nR) Hk). reflexivity. Qed.

  Lemma mp_source_ord_family_ge (k : nat) (Hk : Logic.eq (ltn k nR) false) :
    Logic.eq (mp_source_ord_family nR FR k) O.
  Proof. unfold mp_source_ord_family. rewrite (@insubF _ _ _ k Hk). reflexivity. Qed.

  Lemma mp_ord_family_related :
    SvcNatFunRel (mp_source_ord_family nR FR) (mp_target_ord_family nL fL).
  Proof.
    intros kR kL Hk. unfold mp_target_ord_family.
    have Hlt := mp_nat_lt_correspondence kR kL nR nL Hk Hn.
    destruct (I.Nat_decLt kL nL) as [hL|hL]; cbn.
    - have Hge : Logic.eq (ltn kR nR) false.
      { apply/negbTE/negP. move=> Hsrc.
        exact (match hL (prop_to_sprop _ _ Hlt Hsrc) return Logic.False with end). }
      rewrite (mp_source_ord_family_ge kR Hge). exact (sub_nat_rel_canonical O).
    - have Hsrc : is_true (ltn kR nR) := sprop_to_prop _ _ Hlt hL.
      rewrite (mp_source_ord_family_lt kR Hsrc).
      apply: Hf. exact Hk.
  Qed.

  Theorem mp_fin_sum_related :
    SubNatRel (\sum_(i < nR) FR i)
      (I.Finset_sum_inst3 (Fin nL) Lean.Nat I.Nat_instAddCommMonoid
        (I.Finset_univ_inst1 (Fin nL) (I.Fin_fintype nL)) fL).
  Proof.
    rewrite mp_source_ord_sum_as_interval.
    have Hsum := svc_interval_sum_related O nR Lean.Nat_zero nL
      (mp_source_ord_family nR FR) (mp_target_ord_family nL fL)
      (sub_nat_rel_canonical O) Hn mp_ord_family_related.
    unfold SubNatRel in Hsum |- *.
    exact (sub_imported_eq_trans _ _ _ Hsum
      (sub_imported_eq_sym _ _
        (I.Prosa_Validation_MultiprocessorInterface_production_fin_sum nL fL))).
  Qed.
End FinSum.

(** Regression instances: the empty and the singleton multiprocessor. *)
Lemma mp_fin_sum_related_zero (FR : 'I_0 -> nat) (fL : Fin Lean.Nat_zero -> Lean.Nat) :
  (forall oR oL, MpOrdRel 0 Lean.Nat_zero oR oL -> SubNatRel (FR oR) (fL oL)) ->
  SubNatRel (\sum_(i < 0) FR i)
    (I.Finset_sum_inst3 (Fin Lean.Nat_zero) Lean.Nat I.Nat_instAddCommMonoid
      (I.Finset_univ_inst1 (Fin Lean.Nat_zero) (I.Fin_fintype Lean.Nat_zero)) fL).
Proof. exact (mp_fin_sum_related 0 Lean.Nat_zero (sub_nat_rel_canonical 0) FR fL). Qed.

Lemma mp_fin_sum_related_one (FR : 'I_1 -> nat) (fL : Fin (sub_nat_to_imported 1) -> Lean.Nat) :
  (forall oR oL, MpOrdRel 1 (sub_nat_to_imported 1) oR oL -> SubNatRel (FR oR) (fL oL)) ->
  SubNatRel (\sum_(i < 1) FR i)
    (I.Finset_sum_inst3 (Fin (sub_nat_to_imported 1)) Lean.Nat I.Nat_instAddCommMonoid
      (I.Finset_univ_inst1 (Fin (sub_nat_to_imported 1))
        (I.Fin_fintype (sub_nat_to_imported 1))) fL).
Proof. exact (mp_fin_sum_related 1 _ (sub_nat_rel_canonical 1) FR fL). Qed.

(** * Multiprocessor states and per-processor observations *)

Section Multiprocessor.
  Context (Job : eqType).
  Let dJ := svc_decidable_eq Job.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Hypothesis Hsupply_on : forall sR sL cR, svc_ps_state_rel Job PStateR PStateL R sR sL ->
    SubNatRel (@prosa.behavior.schedule.supply_on Job PStateR sR cR)
      (I.Prosa_Behavior_Schedule_ProcessorState_supply_on Job dJ PStateL sL
        (svc_ps_core_to_target Job PStateR PStateL R cR)).

  Variables (nR : nat) (nL : Lean.Nat).
  Hypothesis Hn : SubNatRel nR nL.

  Let MpsR := prosa.model.processor.multiprocessor.multiprocessor_state Job PStateR nR.
  Let MpsL := I.Prosa_Model_Processor_Multiprocessor_multiprocessor_state Job dJ PStateL nL.

  Definition MpStateRel (mR : MpsR) (mL : MpsL) : SProp :=
    forall oR oL, MpOrdRel nR nL oR oL ->
      svc_ps_state_rel Job PStateR PStateL R (mR oR) (mL oL).

  Theorem multiprocessor_state_source_total (mR : MpsR) :
    MpStateRel mR (fun oL => svc_ps_state_to_target Job PStateR PStateL R
      (mR (mp_fin_to_ord nR nL Hn oL))).
  Proof.
    intros oR oL Ho. rewrite (mp_ord_rel_source_unique nR nL Hn oR oL Ho).
    exact (svc_ps_state_rel_canonical Job PStateR PStateL R (mR oR)).
  Qed.

  Theorem multiprocessor_state_target_total (mL : MpsL) :
    MpStateRel ((fun oR => svc_ps_state_to_source Job PStateR PStateL R
      (mL (mp_ord_to_fin nR nL Hn oR))) : MpsR) mL.
  Proof.
    intros oR oL Ho. cbn.
    destruct (mp_ord_rel_target_unique nR nL Hn oR oL Ho).
    exact (svc_ps_state_rel_surjective Job PStateR PStateL R (mL (mp_ord_to_fin nR nL Hn oR))).
  Qed.

  Lemma mp_supply_in_related (sR : @prosa.behavior.schedule.State Job PStateR)
      (sL : I.Prosa_Behavior_Schedule_ProcessorState_State Job dJ PStateL) :
    svc_ps_state_rel Job PStateR PStateL R sR sL ->
    SubNatRel (@prosa.behavior.schedule.supply_in Job PStateR sR)
      (I.Prosa_Behavior_Schedule_ProcessorState_supply_in Job dJ PStateL sL).
  Proof.
    intro Hstate.
    have Hsum := svc_finite_sum_related (@prosa.behavior.schedule.Core Job PStateR)
      (I.Prosa_Behavior_Schedule_ProcessorState_Core Job dJ PStateL)
      (svc_ps_core_to_target Job PStateR PStateL R)
      (fun cR => @prosa.behavior.schedule.supply_on Job PStateR sR cR)
      (fun cL => I.Prosa_Behavior_Schedule_ProcessorState_supply_on Job dJ PStateL sL cL)
      (I.Prosa_Validation_ScheduleInterface_coreEnumeration Job dJ PStateL)
      (fun cR => Hsupply_on sR sL cR Hstate)
      (svc_ps_core_enumeration_rel Job PStateR PStateL R).
    unfold SubNatRel in Hsum |- *.
    exact (sub_imported_eq_trans _ _ _ Hsum
      (sub_imported_eq_sym _ _
        (I.Prosa_Validation_ScheduleInterface_production_supply_in_as_list_sum
          Job dJ PStateL sL))).
  Qed.

  Theorem multiproc_scheduled_on_correspondence (j : Job) (mR : MpsR) (mL : MpsL)
      (oR : 'I_nR) (oL : Fin nL) :
    MpStateRel mR mL -> MpOrdRel nR nL oR oL ->
    SvcBoolRel (prosa.model.processor.multiprocessor.multiproc_scheduled_on Job PStateR nR j mR oR)
      (I.Prosa_Model_Processor_Multiprocessor_multiproc_scheduled_on Job dJ PStateL nL j mL oL).
  Proof.
    intros Hm Ho.
    exact (svc_scheduled_in_related Job PStateR PStateL R j _ _ (Hm oR oL Ho)).
  Qed.

  Theorem multiproc_supply_on_correspondence (mR : MpsR) (mL : MpsL)
      (oR : 'I_nR) (oL : Fin nL) :
    MpStateRel mR mL -> MpOrdRel nR nL oR oL ->
    SubNatRel (prosa.model.processor.multiprocessor.multiproc_supply_on Job PStateR nR mR oR)
      (I.Prosa_Model_Processor_Multiprocessor_multiproc_supply_on Job dJ PStateL nL mL oL).
  Proof.
    intros Hm Ho. exact (mp_supply_in_related _ _ (Hm oR oL Ho)).
  Qed.

  Theorem multiproc_service_on_correspondence (j : Job) (mR : MpsR) (mL : MpsL)
      (oR : 'I_nR) (oL : Fin nL) :
    MpStateRel mR mL -> MpOrdRel nR nL oR oL ->
    SubNatRel (prosa.model.processor.multiprocessor.multiproc_service_on Job PStateR nR j mR oR)
      (I.Prosa_Model_Processor_Multiprocessor_multiproc_service_on Job dJ PStateL nL j mL oL).
  Proof.
    intros Hm Ho.
    exact (svc_service_in_related Job PStateR PStateL R j _ _ (Hm oR oL Ho)).
  Qed.

  (** The core sum of the multiprocessor instance, on both sides. *)
  Lemma mp_core_sum_related (j : Job) (mR : MpsR) (mL : MpsL) :
    MpStateRel mR mL ->
    SubNatRel (\sum_(cpu < nR) @prosa.behavior.schedule.service_in Job PStateR j (mR cpu))
      (I.Finset_sum_inst3 (Fin nL) Lean.Nat I.Nat_instAddCommMonoid
        (I.Finset_univ_inst1 (Fin nL) (I.Fin_fintype nL))
        (fun cpu => I.Prosa_Behavior_Schedule_ProcessorState_service_in Job dJ PStateL j (mL cpu))).
  Proof.
    intro Hm. apply: mp_fin_sum_related; first exact Hn.
    intros oR oL Ho.
    exact (svc_service_in_related Job PStateR PStateL R j _ _ (Hm oR oL Ho)).
  Qed.
  (** The service of the multiprocessor instance is, on both sides and by
      definition, the core sum above. *)
  Lemma mp_multiproc_service_in_related (j : Job) (mR : MpsR) (mL : MpsL) :
    MpStateRel mR mL ->
    SubNatRel (@prosa.behavior.schedule.service_in Job
        (prosa.model.processor.multiprocessor.multiproc_state Job PStateR nR) j mR)
      (I.Prosa_Behavior_Schedule_ProcessorState_service_in_inst4 Job dJ
        (I.Prosa_Model_Processor_Multiprocessor_multiproc_state Job dJ PStateL nL) j mL).
  Proof. intro Hm. exact (mp_core_sum_related j mR mL Hm). Qed.

  Theorem multiproc_service_in_eq_correspondence :
    PropSPropRel
      (forall (j : Job) (mps : MpsR),
        Logic.eq (@prosa.behavior.schedule.service_in Job
            (prosa.model.processor.multiprocessor.multiproc_state Job PStateR nR) j mps)
          (\sum_(cpu < nR) @prosa.behavior.schedule.service_in Job PStateR j (mps cpu)))
      (forall (j : Job) (mps : MpsL),
        Lean.eq (I.Prosa_Behavior_Schedule_ProcessorState_service_in_inst4 Job dJ
            (I.Prosa_Model_Processor_Multiprocessor_multiproc_state Job dJ PStateL nL) j mps)
          (I.Finset_sum_inst3 (Fin nL) I.Prosa_Behavior_Job_work I.Nat_instAddCommMonoid
            (I.Finset_univ_inst1 (Fin nL) (I.Fin_fintype nL))
            (fun cpu => I.Prosa_Behavior_Schedule_ProcessorState_service_in Job dJ PStateL j (mps cpu)))).
  Proof.
    split.
    - intros HR j mL.
      pose mR := ((fun oR => svc_ps_state_to_source Job PStateR PStateL R
        (mL (mp_ord_to_fin nR nL Hn oR))) : MpsR).
      have Hm : MpStateRel mR mL := multiprocessor_state_target_total mL.
      exact (prop_to_sprop _ _ (sub_nat_eq_correspondence _ _ _ _
        (mp_multiproc_service_in_related j mR mL Hm) (mp_core_sum_related j mR mL Hm)) (HR j mR)).
    - intros HL j mR.
      pose mL := ((fun oL => svc_ps_state_to_target Job PStateR PStateL R
        (mR (mp_fin_to_ord nR nL Hn oL))) : MpsL).
      have Hm : MpStateRel mR mL := multiprocessor_state_source_total mR.
      exact (sprop_to_prop _ _ (sub_nat_eq_correspondence _ _ _ _
        (mp_multiproc_service_in_related j mR mL Hm) (mp_core_sum_related j mR mL Hm)) (HL j mL)).
  Qed.
End Multiprocessor.
