From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import ProgressSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedProgress ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations.

Module I := ImportedProgress.
Module S := ProgressSemanticSource.ProgressSemanticSource.

(** Correspondences for [analysis/definitions/progress.v]: for related
    processor states (two-sided [SvcProcessorStateRel]) and schedules, the
    three extracted source definitions and the compiled Lean definitions are
    related; the remark statement (source side: the extracted elaborated
    statement specialised at the job type, processor state and schedule;
    target side: the imported Lean theorem type) is related with the job an
    identity carrier and the instants covered in both directions.  Service is
    the accepted Service proof re-instantiated at this artifact. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma pg_imp_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P -> Q) (PL -> QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros H p. exact (prop_to_sprop _ _ HQ (H (sprop_to_prop _ _ HP p))).
  - intro H. apply strictly_inhabits. intro p.
    exact (sprop_to_prop _ _ HQ (H (prop_to_sprop _ _ HP p))).
Qed.

Lemma pg_forall_nat_correspondence (PR : nat -> Prop) (PL : Lean.Nat -> SProp) :
  (forall nR nL, SubNatRel nR nL -> PropSPropRel (PR nR) (PL nL)) ->
  PropSPropRel (forall nR, PR nR) (forall nL, PL nL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros HR nL. exact (prop_to_sprop _ _ (HP _ _ (sub_nat_rel_surjective nL))
      (HR (sub_nat_to_rocq nL))).
  - intro HL. apply strictly_inhabits. intro nR.
    exact (sprop_to_prop _ _ (HP _ _ (sub_nat_rel_canonical nR)) (HL (sub_nat_to_imported nR))).
Qed.

Lemma pg_forall_identity_correspondence (T : Type) (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) -> PropSPropRel (forall x, PR x) (forall x, PL x).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros HR x. exact (prop_to_sprop _ _ (HP x) (HR x)).
  - intro HL. apply strictly_inhabits. intro x. exact (sprop_to_prop _ _ (HP x) (HL x)).
Qed.

Lemma pg_iff_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P <-> Q) (I.Iff PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [HPQ HQP]. exact (I.Iff_intro PL QL
      (fun p => prop_to_sprop _ _ HQ (HPQ (sprop_to_prop _ _ HP p)))
      (fun q => prop_to_sprop _ _ HP (HQP (sprop_to_prop _ _ HQ q)))).
  - intro H. apply strictly_inhabits. split.
    + intro p. apply (sprop_to_prop _ _ HQ).
      exact (I.Iff_mp PL QL H (prop_to_sprop _ _ HP p)).
    + intro q. apply (sprop_to_prop _ _ HP).
      exact (I.Iff_mpr PL QL H (prop_to_sprop _ _ HQ q)).
Qed.

Section Progress.
  Context (Job : eqType).
  Let dJ := svc_decidable_eq Job.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

  Lemma pg_service_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@prosa.behavior.service.service_at Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_service_at Job dJ PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.service_at.
    cbn [I.Prosa_Behavior_Service_service_at].
    exact (svc_service_in_related Job PStateR PStateL R j (schedR tR) (schedL tL) (Hsched tR tL Ht)).
  Qed.

  Lemma pg_service_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@prosa.behavior.service.service Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_service Job dJ PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.service.
    cbn [I.Prosa_Behavior_Service_service].
    have Hsum := svc_interval_sum_related O tR Lean.Nat_zero tL
      (fun t => @prosa.behavior.service.service_at Job PStateR schedR j t)
      (fun t => I.Prosa_Behavior_Service_service_at Job dJ PStateL schedL j t)
      (sub_nat_rel_canonical O) Ht (fun xR xL Hx => pg_service_at_related j xR xL Hx).
    change (SubNatRel
      (@prosa.behavior.service.service_during Job PStateR schedR j O tR)
      (I.Prosa_Validation_ServiceInterface_serviceDuringProjection
        Job dJ PStateL schedL j Lean.Nat_zero tL)) in Hsum.
    exact Hsum.
  Qed.

  Theorem job_has_progressed_correspondence (j : Job) (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SvcBoolRel (@S.job_has_progressed Job PStateR schedR j t1R t2R)
      (I.Prosa_Analysis_Definitions_Progress_job_has_progressed Job dJ PStateL schedL j t1L t2L).
  Proof.
    intros H1 H2. unfold S.job_has_progressed.
    cbn [I.Prosa_Analysis_Definitions_Progress_job_has_progressed].
    exact (svc_decide_lt_related _ _ _ _ (pg_service_related j _ _ H1) (pg_service_related j _ _ H2)).
  Qed.

  Theorem no_progress_correspondence (j : Job) (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SvcBoolRel (@S.no_progress Job PStateR schedR j t1R t2R)
      (I.Prosa_Analysis_Definitions_Progress_no_progress Job dJ PStateL schedL j t1L t2L).
  Proof.
    intros H1 H2. unfold S.no_progress.
    cbn [I.Prosa_Analysis_Definitions_Progress_no_progress].
    exact (svc_decide_eq_related _ _ _ _ (pg_service_related j _ _ H1) (pg_service_related j _ _ H2)).
  Qed.

  Theorem no_progress_for_correspondence (j : Job) (tR dR : nat) (tL dL : Lean.Nat) :
    SubNatRel tR tL -> SubNatRel dR dL ->
    SvcBoolRel (@S.no_progress_for Job PStateR schedR j tR dR)
      (I.Prosa_Analysis_Definitions_Progress_no_progress_for Job dJ PStateL schedL j tL dL).
  Proof.
    intros Ht Hd. unfold S.no_progress_for.
    cbn [I.Prosa_Analysis_Definitions_Progress_no_progress_for].
    exact (no_progress_correspondence j _ _ _ _ (svc_target_sub_related _ _ _ _ Ht Hd) Ht).
  Qed.

  Definition src_no_progress_equiv : Prop :=
    ltac:(body_of (fun s : S.statement_no_progress_equiv => s Job PStateR schedR)).
  Definition tgt_no_progress_equiv : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Definitions_Progress_no_progress_equiv Job dJ PStateL schedL)).

  Theorem no_progress_equiv_correspondence : PropSPropRel src_no_progress_equiv tgt_no_progress_equiv.
  Proof.
    apply pg_forall_identity_correspondence. intro j.
    apply pg_forall_nat_correspondence. intros t1R t1L H1.
    apply pg_forall_nat_correspondence. intros t2R t2L H2.
    apply pg_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ H1 H2)|].
    apply pg_iff_correspondence.
    - exact (svc_bool_truth_correspondence _ _
        (svc_bool_not_related _ _ (job_has_progressed_correspondence j _ _ _ _ H1 H2))).
    - exact (svc_bool_truth_correspondence _ _ (no_progress_correspondence j _ _ _ _ H1 H2)).
  Qed.
End Progress.
