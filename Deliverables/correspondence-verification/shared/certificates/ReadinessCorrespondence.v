From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import ReadinessSemanticSource PreemptionParameterSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedReadiness ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations SequentialityCorrespondence.

Module I := ImportedReadiness.
Module S := ReadinessSemanticSource.ReadinessSemanticSource.
Module PP := PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.

(** Definition certificates for [analysis/definitions/readiness.v]: for
    related inputs (job arrival/cost/task, processor state with the two-sided
    [SvcProcessorStateRel], a readiness model related pointwise on Booleans
    over related schedules, the [JobPreemptable] class related pointwise as in
    the accepted parameter certificate, arrival sequence) the three extracted
    source definitions and the compiled Lean definitions are related.
    Schedules bound inside the definitions are covered in both directions
    through the processor-state conversion of [SvcProcessorStateRel] (with its
    roundtrips), which also yields the accepted [SvcScheduleRel] and the
    state equalities of [identical_prefix].  Service and [prior_jobs_complete]
    are the accepted proofs re-instantiated at this artifact. *)

Lemma rd_forall_cover_sprop (A B : Type) (Rel : A -> B -> SProp)
    (toB : A -> B) (toA : B -> A)
    (HtoB : forall a, Rel a (toB a)) (HtoA : forall b, Rel (toA b) b)
    (PR : A -> Prop) (PL : B -> SProp) :
  (forall a b, Rel a b -> PropSPropRel (PR a) (PL b)) ->
  PropSPropRel (forall a, PR a) (forall b, PL b).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR b. exact (prop_to_sprop _ _ (H _ _ (HtoA b)) (HR (toA b))).
  - intro HL. apply strictly_inhabits. intro a.
    exact (sprop_to_prop _ _ (H _ _ (HtoB a)) (HL (toB a))).
Qed.

Lemma rd_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma rd_nat_input (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
Qed.

Lemma rd_bool_eq_correspondence (bR cR : bool) (bL cL : I.Bool) :
  SvcBoolRel bR bL -> SvcBoolRel cR cL -> PropSPropRel (bR = cR) (Lean.eq bL cL).
Proof.
  intros Hb Hc. apply prop_sprop_rel_intro.
  - intro E. destruct E.
    exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Hb) Hc).
  - intro E. apply strictly_inhabits.
    have EL := imported_eq_to_coq_eq _ _
      (sub_imported_eq_trans _ _ _ Hb (sub_imported_eq_trans _ _ _ E (sub_imported_eq_sym _ _ Hc))).
    destruct bR, cR; cbn in EL; solve [reflexivity | discriminate EL].
Qed.

Section Readiness.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable readyR : @prosa.behavior.ready.JobReady Job PStateR costR jaR.
  Variable readyL : I.Prosa_Behavior_Ready_JobReady Job dJ PStateL costL jaL.

  Definition RdJobReadyRel : SProp :=
    forall schedR' schedL',
      SvcScheduleRel Job PStateR PStateL R schedR' schedL' ->
    forall (j : Job) (tR : nat) (tL : Lean.Nat),
      SubNatRel tR tL ->
      SvcBoolRel
        (@prosa.behavior.ready.job_ready Job PStateR costR jaR readyR schedR' j tR)
        (I.Prosa_Behavior_Ready_JobReady_job_ready Job dJ PStateL costL jaL readyL schedL' j tL).
  Hypothesis Hready : RdJobReadyRel.

  (** Schedules related through the processor-state conversion. *)
  Definition RdScheduleFunRel (schedR : @prosa.behavior.schedule.schedule Job PStateR)
      (schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL) : SProp :=
    forall tR tL, SubNatRel tR tL ->
      Lean.eq (svc_ps_state_to_target Job PStateR PStateL R (schedR tR)) (schedL tL).

  Lemma rd_schedule_fun_to_svc schedR schedL :
    RdScheduleFunRel schedR schedL -> SvcScheduleRel Job PStateR PStateL R schedR schedL.
  Proof.
    intros Hf tR tL Ht.
    exact (rd_lean_transport (fun sL => svc_ps_state_rel Job PStateR PStateL R (schedR tR) sL)
      _ _ (Hf tR tL Ht) (svc_ps_state_rel_canonical Job PStateR PStateL R (schedR tR))).
  Qed.

  Definition rd_schedule_to_target (schedR : @prosa.behavior.schedule.schedule Job PStateR) :
      I.Prosa_Behavior_Schedule_schedule Job dJ PStateL :=
    fun tL => svc_ps_state_to_target Job PStateR PStateL R (schedR (sub_nat_to_rocq tL)).

  Definition rd_schedule_to_source (schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL) :
      @prosa.behavior.schedule.schedule Job PStateR :=
    fun tR => svc_ps_state_to_source Job PStateR PStateL R (schedL (sub_nat_to_imported tR)).

  Lemma rd_schedule_to_target_rel schedR : RdScheduleFunRel schedR (rd_schedule_to_target schedR).
  Proof.
    intros tR tL Ht. unfold rd_schedule_to_target.
    rewrite (rd_nat_input _ _ Ht). exact (@Lean.eq_refl _ _).
  Qed.

  Lemma rd_schedule_to_source_rel schedL : RdScheduleFunRel (rd_schedule_to_source schedL) schedL.
  Proof.
    intros tR tL Ht. unfold rd_schedule_to_source.
    exact (sub_imported_eq_trans _ _ _
      (svc_ps_state_target_roundtrip Job PStateR PStateL R _)
      (sub_imported_eq_congr schedL _ _ Ht)).
  Qed.

  Let cover_schedule :=
    rd_forall_cover_sprop _ _ RdScheduleFunRel rd_schedule_to_target rd_schedule_to_source
      rd_schedule_to_target_rel rd_schedule_to_source_rel.

  Lemma rd_state_eq_correspondence schedR schedR' schedL schedL'
      (Hf : RdScheduleFunRel schedR schedL) (Hf' : RdScheduleFunRel schedR' schedL')
      (tR : nat) (tL : Lean.Nat) (Ht : SubNatRel tR tL) :
    PropSPropRel (schedR tR = schedR' tR) (Lean.eq (schedL tL) (schedL' tL)).
  Proof.
    apply prop_sprop_rel_intro.
    - intro E.
      exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ (Hf tR tL Ht))
        (sub_imported_eq_trans _ _ _
          (coq_eq_to_imported_eq _ _ (f_equal (svc_ps_state_to_target Job PStateR PStateL R) E))
          (Hf' tR tL Ht))).
    - intro EL. apply strictly_inhabits.
      have ET := imported_eq_to_coq_eq _ _
        (sub_imported_eq_trans _ _ _ (Hf tR tL Ht)
          (sub_imported_eq_trans _ _ _ EL (sub_imported_eq_sym _ _ (Hf' tR tL Ht)))).
      have ES := f_equal (svc_ps_state_to_source Job PStateR PStateL R) ET.
      rewrite !(svc_ps_state_source_roundtrip Job PStateR PStateL R) in ES.
      exact ES.
  Qed.

  Lemma rd_identical_prefix_correspondence schedR schedR' schedL schedL'
      (Hf : RdScheduleFunRel schedR schedL) (Hf' : RdScheduleFunRel schedR' schedL')
      (hR : nat) (hL : Lean.Nat) (Hh : SubNatRel hR hL) :
    PropSPropRel (@prosa.analysis.definitions.schedule_prefix.identical_prefix
        Job PStateR schedR schedR' hR)
      (I.Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix
        Job dJ PStateL schedL schedL' hL).
  Proof.
    unfold prosa.analysis.definitions.schedule_prefix.identical_prefix.
    cbn [I.Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ Ht Hh)|].
    exact (rd_state_eq_correspondence _ _ _ _ Hf Hf' tR tL Ht).
  Qed.

  Lemma rd_service_at_related schedR schedL (Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL)
      (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@prosa.behavior.service.service_at Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_service_at Job dJ PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.service_at.
    cbn [I.Prosa_Behavior_Service_service_at].
    exact (svc_service_in_related Job PStateR PStateL R j (schedR tR) (schedL tL) (Hsched tR tL Ht)).
  Qed.

  Lemma rd_service_related schedR schedL (Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL)
      (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@prosa.behavior.service.service Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_service Job dJ PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.service.
    cbn [I.Prosa_Behavior_Service_service].
    have Hsum := svc_interval_sum_related O tR Lean.Nat_zero tL
      (fun t => @prosa.behavior.service.service_at Job PStateR schedR j t)
      (fun t => I.Prosa_Behavior_Service_service_at Job dJ PStateL schedL j t)
      (sub_nat_rel_canonical O) Ht (fun xR xL Hx => rd_service_at_related schedR schedL Hsched j xR xL Hx).
    change (SubNatRel
      (@prosa.behavior.service.service_during Job PStateR schedR j O tR)
      (I.Prosa_Validation_ServiceInterface_serviceDuringProjection
        Job dJ PStateL schedL j Lean.Nat_zero tL)) in Hsum.
    exact Hsum.
  Qed.

  (** *** Non-clairvoyance *)

  Theorem nonclairvoyant_readiness_correspondence :
    PropSPropRel (@S.nonclairvoyant_readiness Job costR jaR PStateR readyR)
      (I.Prosa_Analysis_Definitions_Readiness_nonclairvoyant_readiness
        Job dJ costL jaL PStateL readyL).
  Proof.
    unfold S.nonclairvoyant_readiness.
    cbn [I.Prosa_Analysis_Definitions_Readiness_nonclairvoyant_readiness].
    apply cover_schedule. intros schedR schedL Hf.
    apply cover_schedule. intros schedR' schedL' Hf'.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros hR hL Hh.
    apply ar_imp_correspondence; [exact (rd_identical_prefix_correspondence _ _ _ _ Hf Hf' hR hL Hh)|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Ht Hh)|].
    exact (rd_bool_eq_correspondence _ _ _ _
      (Hready schedR schedL (rd_schedule_fun_to_svc _ _ Hf) j tR tL Ht)
      (Hready schedR' schedL' (rd_schedule_fun_to_svc _ _ Hf') j tR tL Ht)).
  Qed.

  (** *** Nonpreemptive readiness *)

  Section Preemption.
    Variable jpR : PP.JobPreemptable Job.
    Variable jpL : I.Prosa_Model_Preemption_Parameter_JobPreemptable Job dJ.
    Hypothesis Hjp : forall (j : Job) (nR : nat) (nL : Lean.Nat), SubNatRel nR nL ->
      SvcBoolRel (@PP.job_preemptable Job jpR j nR)
        (I.Prosa_Model_Preemption_Parameter_JobPreemptable_job_preemptable Job dJ jpL j nL).
    Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
    Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
    Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

    Theorem valid_nonpreemptive_readiness_correspondence :
      PropSPropRel (@S.valid_nonpreemptive_readiness Job costR jaR PStateR readyR jpR schedR)
        (I.Prosa_Analysis_Definitions_Readiness_valid_nonpreemptive_readiness
          Job dJ costL jaL PStateL readyL jpL schedL).
    Proof.
      unfold S.valid_nonpreemptive_readiness.
      cbn [I.Prosa_Analysis_Definitions_Readiness_valid_nonpreemptive_readiness].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence.
      - exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _
          (Hjp j _ _ (rd_service_related schedR schedL Hsched j tR tL Ht)))).
      - exact (svc_bool_truth_correspondence _ _ (Hready schedR schedL Hsched j tR tL Ht)).
    Qed.
  End Preemption.

  (** *** Sequential readiness *)

  Section Sequential.
    Context (Task : eqType).
    Let dT := ar_decidable_eq Task.
    Variable jtR : prosa.model.task.concept.JobTask Job Task.
    Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
    Hypothesis Hjt : forall j : Job,
      Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
    Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
    Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
    Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

    Theorem sequential_readiness_correspondence :
      PropSPropRel (@S.sequential_readiness Job costR jaR PStateR readyR Task jtR arrR)
        (I.Prosa_Analysis_Definitions_Readiness_sequential_readiness
          Job dJ costL jaL PStateL readyL Task dT jtL arrL).
    Proof.
      unfold S.sequential_readiness.
      cbn [I.Prosa_Analysis_Definitions_Readiness_sequential_readiness].
      apply cover_schedule. intros schedR schedL Hf.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence.
      - exact (svc_bool_truth_correspondence _ _
          (Hready schedR schedL (rd_schedule_fun_to_svc _ _ Hf) j tR tL Ht)).
      - exact (svc_bool_truth_correspondence _ _
          (prior_jobs_complete_correspondence Job Task jtR jtL Hjt jaR jaL Hja costR costL Hcost
            PStateR PStateL R arrR arrL Harr schedR schedL (rd_schedule_fun_to_svc _ _ Hf) j tR tL Ht)).
    Qed.
  End Sequential.
End Readiness.
