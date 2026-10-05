From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From prosa Require Import model.readiness.basic behavior.service.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedReadinessBasicProjection
  ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence BasicBaseAdapter
  BasicNatBoolOperations BasicIntervalOperations BasicScheduleOperations
  BasicJobOperations ReadinessBasicInterfaceCertificate.

(** Reusable structural relation for a law with Boolean antecedent and
    consequent.  Neither side's law proof is used. *)
Lemma basic_bool_implication_correspondence
    (aR bR : bool)
    (aL bL : ImportedReadinessBasicProjection.Bool) :
  SvcBoolRel aR aL -> SvcBoolRel bR bL ->
  PropSPropRel (is_true aR -> is_true bR)
    (Lean.eq aL ImportedReadinessBasicProjection.Bool_true ->
     Lean.eq bL ImportedReadinessBasicProjection.Bool_true).
Proof.
  intros Ha Hb.
  destruct (svc_bool_truth_correspondence _ _ Ha) as [HaF HaB].
  destruct (svc_bool_truth_correspondence _ _ Hb) as [HbF HbB].
  apply prop_sprop_rel_intro.
  - intros Himp HaL. exact (HbF (Himp (HaB HaL))).
  - intro HimpL. apply strictly_inhabits.
    intro HaR. exact (HbB (HimpL (HaF HaR))).
Qed.

(** The actual imported Basic artifact has its own Lean Nat/Bool/List identity.
    These are the smallest accepted Service operation proofs re-instantiated
    at that identity, followed by the local JobReady field correspondence. *)
Section BasicPendingCorrespondence.
  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedReadinessBasicProjection.Prosa_Behavior_Schedule_ProcessorState
      Job (svc_decidable_eq Job).
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : ImportedReadinessBasicProjection.Prosa_Behavior_Schedule_schedule
    Job (svc_decidable_eq Job) PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : ImportedReadinessBasicProjection.Prosa_Behavior_Job_JobCost
    Job (svc_decidable_eq Job).
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable arrivalR : prosa.behavior.job.JobArrival Job.
  Variable arrivalL : ImportedReadinessBasicProjection.Prosa_Behavior_Job_JobArrival
    Job (svc_decidable_eq Job).
  Hypothesis Harrival : SvcJobArrivalRel Job arrivalR arrivalL.

  Lemma basic_service_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@prosa.behavior.service.service_at Job PStateR schedR j tR)
      (ImportedReadinessBasicProjection.Prosa_Behavior_Service_service_at
        Job (svc_decidable_eq Job) PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.service_at.
    cbn [ImportedReadinessBasicProjection.Prosa_Behavior_Service_service_at].
    exact (svc_service_in_related Job PStateR PStateL R j
      (schedR tR) (schedL tL) (Hsched tR tL Ht)).
  Qed.

  Lemma basic_service_during_related (j : Job)
      (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel (@prosa.behavior.service.service_during Job PStateR
        schedR j t1R t2R)
      (ImportedReadinessBasicProjection.Prosa_Behavior_Service_service_during
        Job (svc_decidable_eq Job) PStateL schedL j t1L t2L).
  Proof.
    intros Ht1 Ht2.
    have Hsum := svc_interval_sum_related t1R t2R t1L t2L
      (fun t => @prosa.behavior.service.service_at Job PStateR schedR j t)
      (fun t => ImportedReadinessBasicProjection.Prosa_Behavior_Service_service_at
        Job (svc_decidable_eq Job) PStateL schedL j t)
      Ht1 Ht2 (fun tR tL Ht => basic_service_at_related j tR tL Ht).
    change (SubNatRel
      (@prosa.behavior.service.service_during Job PStateR schedR j t1R t2R)
      (ImportedReadinessBasicProjection.Prosa_Validation_ServiceInterface_serviceDuringProjection
        Job (svc_decidable_eq Job) PStateL schedL j t1L t2L)) in Hsum.
    exact Hsum.
  Qed.

  Lemma basic_service_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@prosa.behavior.service.service Job PStateR schedR j tR)
      (ImportedReadinessBasicProjection.Prosa_Behavior_Service_service
        Job (svc_decidable_eq Job) PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.service.
    cbn [ImportedReadinessBasicProjection.Prosa_Behavior_Service_service].
    exact (basic_service_during_related j O tR Lean.Nat_zero tL
      (sub_nat_rel_canonical O) Ht).
  Qed.

  Lemma basic_completed_by_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.service.completed_by Job PStateR
        schedR costR j tR)
      (ImportedReadinessBasicProjection.Prosa_Behavior_Service_completed_by
        Job (svc_decidable_eq Job) PStateL schedL costL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.completed_by.
    cbn [ImportedReadinessBasicProjection.Prosa_Behavior_Service_completed_by].
    exact (svc_decide_le_related _ _ _ _ (Hcost j)
      (basic_service_related j tR tL Ht)).
  Qed.

  Lemma basic_pending_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.service.pending Job PStateR
        schedR costR arrivalR j tR)
      (ImportedReadinessBasicProjection.Prosa_Behavior_Service_pending
        Job (svc_decidable_eq Job) PStateL schedL costL arrivalL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.pending.
    cbn [ImportedReadinessBasicProjection.Prosa_Behavior_Service_pending].
    apply svc_bool_and_related.
    - exact (svc_has_arrived_related Job arrivalR arrivalL j
        Harrival tR tL Ht).
    - exact (svc_bool_not_related _ _
        (basic_completed_by_related j tR tL Ht)).
  Qed.

  Lemma basic_ready_field_correspondence (j : Job)
      (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel
      (@prosa.behavior.ready.job_ready Job PStateR costR arrivalR
        (@prosa.model.readiness.basic.basic_ready_instance
          Job PStateR arrivalR costR) schedR j tR)
      (ImportedReadinessBasicProjection.Prosa_Behavior_Ready_JobReady_job_ready
        Job (svc_decidable_eq Job) PStateL costL arrivalL
        (ImportedReadinessBasicProjection.Prosa_Model_Readiness_Basic_basic_ready_instance
          Job (svc_decidable_eq Job) PStateL arrivalL costL)
        schedL j tL).
  Proof.
    intro Ht.
    cbn [prosa.behavior.ready.job_ready
      prosa.model.readiness.basic.basic_ready_instance
      ImportedReadinessBasicProjection.Prosa_Behavior_Ready_JobReady_job_ready
      ImportedReadinessBasicProjection.Prosa_Model_Readiness_Basic_basic_ready_instance].
    exact (basic_pending_related j tR tL Ht).
  Qed.

  (** This checks the structure of the source and imported JobReady law
      statements under related inputs.  It deliberately does not invoke
      either law proof field. *)
  Lemma basic_ready_law_statement_correspondence (j : Job)
      (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    PropSPropRel
      (is_true (@prosa.behavior.ready.job_ready Job PStateR costR arrivalR
        (@prosa.model.readiness.basic.basic_ready_instance
          Job PStateR arrivalR costR) schedR j tR) ->
       is_true (@prosa.behavior.service.pending Job PStateR
         schedR costR arrivalR j tR))
      (Lean.eq
        (ImportedReadinessBasicProjection.Prosa_Behavior_Ready_JobReady_job_ready
          Job (svc_decidable_eq Job) PStateL costL arrivalL
          (ImportedReadinessBasicProjection.Prosa_Model_Readiness_Basic_basic_ready_instance
            Job (svc_decidable_eq Job) PStateL arrivalL costL)
          schedL j tL)
        ImportedReadinessBasicProjection.Bool_true ->
       Lean.eq
        (ImportedReadinessBasicProjection.Prosa_Behavior_Service_pending
          Job (svc_decidable_eq Job) PStateL schedL costL arrivalL j tL)
        ImportedReadinessBasicProjection.Bool_true).
  Proof.
    intro Ht. apply basic_bool_implication_correspondence.
    - exact (basic_ready_field_correspondence j tR tL Ht).
    - exact (basic_pending_related j tR tL Ht).
  Qed.
End BasicPendingCorrespondence.

Print Assumptions basic_service_at_related.
Print Assumptions basic_service_during_related.
Print Assumptions basic_service_related.
Print Assumptions basic_completed_by_related.
Print Assumptions basic_pending_related.
Print Assumptions basic_ready_field_correspondence.
Print Assumptions basic_bool_implication_correspondence.
Print Assumptions basic_ready_law_statement_correspondence.
