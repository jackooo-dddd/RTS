From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From prosa Require Import model.readiness.jitter behavior.service.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedReadinessJitterProjection
  ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence JitterSvcBaseAdapter
  JitterSvcNatBoolOperations JitterSvcIntervalOperations JitterSvcScheduleOperations
  JitterSvcJobOperations.

(** Reusable structural relation for a law with Boolean antecedent and
    consequent.  Neither side's law proof is used. *)
Lemma jitter_bool_implication_correspondence
    (aR bR : bool)
    (aL bL : ImportedReadinessJitterProjection.Bool) :
  SvcBoolRel aR aL -> SvcBoolRel bR bL ->
  PropSPropRel (is_true aR -> is_true bR)
    (Lean.eq aL ImportedReadinessJitterProjection.Bool_true ->
     Lean.eq bL ImportedReadinessJitterProjection.Bool_true).
Proof.
  intros Ha Hb.
  destruct (svc_bool_truth_correspondence _ _ Ha) as [HaF HaB].
  destruct (svc_bool_truth_correspondence _ _ Hb) as [HbF HbB].
  apply prop_sprop_rel_intro.
  - intros Himp HaL. exact (HbF (Himp (HaB HaL))).
  - intro HimpL. apply strictly_inhabits.
    intro HaR. exact (HbB (HimpL (HaF HaR))).
Qed.

(** The actual imported Jitter artifact has its own Lean Nat/Bool/List identity.
    These are the smallest accepted Service operation proofs re-instantiated
    at that identity, followed by the local JobReady field correspondence. *)
Section JitterReadyCorrespondence.
  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedReadinessJitterProjection.Prosa_Behavior_Schedule_ProcessorState
      Job (svc_decidable_eq Job).
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : ImportedReadinessJitterProjection.Prosa_Behavior_Schedule_schedule
    Job (svc_decidable_eq Job) PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : ImportedReadinessJitterProjection.Prosa_Behavior_Job_JobCost
    Job (svc_decidable_eq Job).
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable arrivalR : prosa.behavior.job.JobArrival Job.
  Variable arrivalL : ImportedReadinessJitterProjection.Prosa_Behavior_Job_JobArrival
    Job (svc_decidable_eq Job).
  Hypothesis Harrival : SvcJobArrivalRel Job arrivalR arrivalL.

  Lemma jitter_service_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@prosa.behavior.service.service_at Job PStateR schedR j tR)
      (ImportedReadinessJitterProjection.Prosa_Behavior_Service_service_at
        Job (svc_decidable_eq Job) PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.service_at.
    cbn [ImportedReadinessJitterProjection.Prosa_Behavior_Service_service_at].
    exact (svc_service_in_related Job PStateR PStateL R j
      (schedR tR) (schedL tL) (Hsched tR tL Ht)).
  Qed.

  Lemma jitter_service_during_related (j : Job)
      (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel (@prosa.behavior.service.service_during Job PStateR
        schedR j t1R t2R)
      (ImportedReadinessJitterProjection.Prosa_Behavior_Service_service_during
        Job (svc_decidable_eq Job) PStateL schedL j t1L t2L).
  Proof.
    intros Ht1 Ht2.
    have Hsum := svc_interval_sum_related t1R t2R t1L t2L
      (fun t => @prosa.behavior.service.service_at Job PStateR schedR j t)
      (fun t => ImportedReadinessJitterProjection.Prosa_Behavior_Service_service_at
        Job (svc_decidable_eq Job) PStateL schedL j t)
      Ht1 Ht2 (fun tR tL Ht => jitter_service_at_related j tR tL Ht).
    change (SubNatRel
      (@prosa.behavior.service.service_during Job PStateR schedR j t1R t2R)
      (ImportedReadinessJitterProjection.Prosa_Validation_ServiceInterface_serviceDuringProjection
        Job (svc_decidable_eq Job) PStateL schedL j t1L t2L)) in Hsum.
    exact Hsum.
  Qed.

  Lemma jitter_service_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@prosa.behavior.service.service Job PStateR schedR j tR)
      (ImportedReadinessJitterProjection.Prosa_Behavior_Service_service
        Job (svc_decidable_eq Job) PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.service.
    cbn [ImportedReadinessJitterProjection.Prosa_Behavior_Service_service].
    exact (jitter_service_during_related j O tR Lean.Nat_zero tL
      (sub_nat_rel_canonical O) Ht).
  Qed.

  Lemma jitter_completed_by_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.service.completed_by Job PStateR
        schedR costR j tR)
      (ImportedReadinessJitterProjection.Prosa_Behavior_Service_completed_by
        Job (svc_decidable_eq Job) PStateL schedL costL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.completed_by.
    cbn [ImportedReadinessJitterProjection.Prosa_Behavior_Service_completed_by].
    exact (svc_decide_le_related _ _ _ _ (Hcost j)
      (jitter_service_related j tR tL Ht)).
  Qed.

  Lemma jitter_pending_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.service.pending Job PStateR
        schedR costR arrivalR j tR)
      (ImportedReadinessJitterProjection.Prosa_Behavior_Service_pending
        Job (svc_decidable_eq Job) PStateL schedL costL arrivalL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.pending.
    cbn [ImportedReadinessJitterProjection.Prosa_Behavior_Service_pending].
    apply svc_bool_and_related.
    - exact (svc_has_arrived_related Job arrivalR arrivalL j
        Harrival tR tL Ht).
    - exact (svc_bool_not_related _ _
        (jitter_completed_by_related j tR tL Ht)).
  Qed.

  (** Input relation for the jitter class instance (its only data field). *)
  Variable jitterR : prosa.model.readiness.jitter.JobJitter Job.
  Variable jitterL : ImportedReadinessJitterProjection.Prosa_Model_Readiness_Jitter_JobJitter
    Job (svc_decidable_eq Job).
  Hypothesis Hjitter : forall j : Job,
    SubNatRel (@prosa.model.readiness.jitter.job_jitter Job jitterR j)
      (ImportedReadinessJitterProjection.Prosa_Model_Readiness_Jitter_JobJitter_job_jitter
        Job (svc_decidable_eq Job) jitterL j).

  Lemma is_released_correspondence (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.model.readiness.jitter.is_released Job arrivalR jitterR j tR)
      (ImportedReadinessJitterProjection.Prosa_Model_Readiness_Jitter_is_released
        Job (svc_decidable_eq Job) arrivalL jitterL j tL).
  Proof.
    intro Ht. unfold prosa.model.readiness.jitter.is_released.
    cbn [ImportedReadinessJitterProjection.Prosa_Model_Readiness_Jitter_is_released].
    exact (svc_decide_le_related _ _ _ _
      (svc_target_add_related _ _ _ _ (Harrival j) (Hjitter j)) Ht).
  Qed.

  (** The readiness field of the actual imported [jitter_ready_instance],
      related through the certified [completed_by] correspondence above. *)
  Lemma jitter_ready_field_correspondence (j : Job)
      (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel
      (@prosa.behavior.ready.job_ready Job PStateR costR arrivalR
        (@prosa.model.readiness.jitter.jitter_ready_instance
          Job PStateR arrivalR costR jitterR) schedR j tR)
      (ImportedReadinessJitterProjection.Prosa_Behavior_Ready_JobReady_job_ready
        Job (svc_decidable_eq Job) PStateL costL arrivalL
        (ImportedReadinessJitterProjection.Prosa_Model_Readiness_Jitter_jitter_ready_instance
          Job (svc_decidable_eq Job) arrivalL jitterL PStateL costL)
        schedL j tL).
  Proof.
    intro Ht.
    change (SvcBoolRel
      (@prosa.model.readiness.jitter.is_released Job arrivalR jitterR j tR &&
       ~~ @prosa.behavior.service.completed_by Job PStateR schedR costR j tR)
      (ImportedReadinessJitterProjection.Bool_and
        (ImportedReadinessJitterProjection.Prosa_Model_Readiness_Jitter_is_released
          Job (svc_decidable_eq Job) arrivalL jitterL j tL)
        (ImportedReadinessJitterProjection.Bool_not
          (ImportedReadinessJitterProjection.Prosa_Behavior_Service_completed_by
            Job (svc_decidable_eq Job) PStateL schedL costL j tL)))).
    apply svc_bool_and_related.
    - exact (is_released_correspondence j tR tL Ht).
    - exact (svc_bool_not_related _ _ (jitter_completed_by_related j tR tL Ht)).
  Qed.

  (** Structure of the JobReady law under related inputs; neither law proof
      field is used. *)
  Lemma jitter_ready_law_statement_correspondence (j : Job)
      (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    PropSPropRel
      (is_true (@prosa.behavior.ready.job_ready Job PStateR costR arrivalR
        (@prosa.model.readiness.jitter.jitter_ready_instance
          Job PStateR arrivalR costR jitterR) schedR j tR) ->
       is_true (@prosa.behavior.service.pending Job PStateR
         schedR costR arrivalR j tR))
      (Lean.eq
        (ImportedReadinessJitterProjection.Prosa_Behavior_Ready_JobReady_job_ready
          Job (svc_decidable_eq Job) PStateL costL arrivalL
          (ImportedReadinessJitterProjection.Prosa_Model_Readiness_Jitter_jitter_ready_instance
            Job (svc_decidable_eq Job) arrivalL jitterL PStateL costL)
          schedL j tL)
        ImportedReadinessJitterProjection.Bool_true ->
       Lean.eq
        (ImportedReadinessJitterProjection.Prosa_Behavior_Service_pending
          Job (svc_decidable_eq Job) PStateL schedL costL arrivalL j tL)
        ImportedReadinessJitterProjection.Bool_true).
  Proof.
    intro Ht. apply jitter_bool_implication_correspondence.
    - exact (jitter_ready_field_correspondence j tR tL Ht).
    - exact (jitter_pending_related j tR tL Ht).
  Qed.
End JitterReadyCorrespondence.

(** Carrier coverage for the JobJitter class: both directions and both
    roundtrips on its single data field. *)
Definition JiJitterRel (Job : eqType)
    (jr : prosa.model.readiness.jitter.JobJitter Job)
    (jl : ImportedReadinessJitterProjection.Prosa_Model_Readiness_Jitter_JobJitter Job (svc_decidable_eq Job)) : SProp :=
  forall j : Job,
    SubNatRel (@prosa.model.readiness.jitter.job_jitter Job jr j)
      (ImportedReadinessJitterProjection.Prosa_Model_Readiness_Jitter_JobJitter_job_jitter
        Job (svc_decidable_eq Job) jl j).

Definition ji_import_jitter (Job : eqType)
    (jr : prosa.model.readiness.jitter.JobJitter Job) :
    ImportedReadinessJitterProjection.Prosa_Model_Readiness_Jitter_JobJitter Job (svc_decidable_eq Job) :=
  ImportedReadinessJitterProjection.Prosa_Model_Readiness_Jitter_JobJitter_mk Job (svc_decidable_eq Job)
    (fun j => sub_nat_to_imported
      (@prosa.model.readiness.jitter.job_jitter Job jr j)).

Definition ji_export_jitter (Job : eqType)
    (jl : ImportedReadinessJitterProjection.Prosa_Model_Readiness_Jitter_JobJitter Job (svc_decidable_eq Job)) :
    prosa.model.readiness.jitter.JobJitter Job :=
  fun j => sub_nat_to_rocq
    (ImportedReadinessJitterProjection.Prosa_Model_Readiness_Jitter_JobJitter_job_jitter
      Job (svc_decidable_eq Job) jl j).

Lemma JobJitter_source_total (Job : eqType)
    (jr : prosa.model.readiness.jitter.JobJitter Job) :
  JiJitterRel Job jr (ji_import_jitter Job jr).
Proof. intro j. exact (@Lean.eq_refl _ _). Qed.

Lemma JobJitter_target_total (Job : eqType)
    (jl : ImportedReadinessJitterProjection.Prosa_Model_Readiness_Jitter_JobJitter Job (svc_decidable_eq Job)) :
  JiJitterRel Job (ji_export_jitter Job jl) jl.
Proof. intro j. exact (sub_nat_imported_roundtrip _). Qed.

Lemma JobJitter_source_roundtrip (Job : eqType)
    (jr : prosa.model.readiness.jitter.JobJitter Job) (j : Job) :
  Logic.eq
    (@prosa.model.readiness.jitter.job_jitter Job
      (ji_export_jitter Job (ji_import_jitter Job jr)) j)
    (@prosa.model.readiness.jitter.job_jitter Job jr j).
Proof. exact (sub_nat_rocq_roundtrip _). Qed.

Print Assumptions jitter_completed_by_related.
Print Assumptions jitter_pending_related.
Print Assumptions is_released_correspondence.
Print Assumptions jitter_ready_field_correspondence.
Print Assumptions jitter_ready_law_statement_correspondence.
Print Assumptions JobJitter_source_total.
Print Assumptions JobJitter_target_total.
Print Assumptions JobJitter_source_roundtrip.
