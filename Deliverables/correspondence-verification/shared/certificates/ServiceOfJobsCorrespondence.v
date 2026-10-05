From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import model.aggregate.service_of_jobs.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedServiceOfJobs ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations.

Module I := ImportedServiceOfJobs.

(** Definition certificates for [model/aggregate/service_of_jobs.v]: for
    related inputs (processor state with the two-sided [SvcProcessorStateRel],
    schedule, arrival sequence, job predicate pointwise on Booleans, job list,
    JLFP policy pointwise on Booleans, [job_task] by [Lean.eq], instants) the
    eight source definitions and the compiled Lean definitions are related.
    Service is the accepted Service proof re-instantiated at this artifact;
    filtered sums go through [big_filter] and the accepted [ari_sum_related];
    the derived priority relations replay the accepted [PriorityDerived]
    proofs (Boolean conjunction with the [!=] observation) on this
    artifact's adapter. *)

Lemma soj_sum_filter_related (T : Type) (PR : T -> bool) (PL : T -> I.Bool)
    (FR : T -> nat) (FL : T -> Lean.Nat) xsR xsL :
  ArPredRel PR PL -> (forall x, SubNatRel (FR x) (FL x)) -> ArListRel xsR xsL ->
  SubNatRel (\sum_(x <- xsR | PR x) FR x) (ari_list_sum T FL (ar_target_filter PL xsL)).
Proof.
  intros HP HF Hxs. rewrite -big_filter.
  exact (ari_sum_related T FR FL _ _ HF (ar_filter_related T PR PL xsR xsL HP Hxs)).
Qed.

(** ** Derived priority relations (replayed from the accepted PriorityDerived) *)

Lemma soj_ne_observation (T : eqType) (x y : T) :
  ArBoolRel (x != y)
    (I.Decidable_decide (I.Ne T x y) (I.instDecidableNot (Lean.eq x y) (ar_decidable_eq T x y))).
Proof.
  unfold ar_decidable_eq, ArBoolRel.
  destruct (@eqP T x y); cbn; exact (@Lean.eq_refl _ _).
Qed.

Definition soj_target_decide_ne (T : eqType) (x y : T) : I.Bool :=
  I.Decidable_decide (I.Ne T x y) (I.instDecidableNot (Lean.eq x y) (ar_decidable_eq T x y)).

Lemma soj_ne_observation_transport (T : eqType) (xR yR xL yL : T) :
  Lean.eq xR xL -> Lean.eq yR yL -> ArBoolRel (xR != yR) (soj_target_decide_ne T xL yL).
Proof.
  intros Hx Hy. unfold ArBoolRel.
  exact (sub_imported_eq_trans _ _ _ (soj_ne_observation T xR yR)
    (sub_imported_eq_congr2 (soj_target_decide_ne T) _ _ _ _ Hx Hy)).
Qed.

Definition SojJLFPRel (Job : eqType)
    (pR : prosa.model.priority.definitions.JLFP_policy Job)
    (pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job (ar_decidable_eq Job)) : SProp :=
  forall x y : Job,
    ArBoolRel (@prosa.model.priority.definitions.hep_job Job pR x y)
      (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job (ar_decidable_eq Job) pL x y).

Lemma soj_another_hep_job_related (Job : eqType) pR pL (x y : Job) :
  SojJLFPRel Job pR pL ->
  ArBoolRel (@prosa.model.priority.definitions.another_hep_job Job pR x y)
    (I.Prosa_Model_Priority_Definitions_another_hep_job Job (ar_decidable_eq Job) pL x y).
Proof.
  intro Hp. unfold prosa.model.priority.definitions.another_hep_job,
    I.Prosa_Model_Priority_Definitions_another_hep_job.
  exact (ar_bool_and_related _ _ _ _ (Hp x y) (soj_ne_observation Job x y)).
Qed.

Lemma soj_another_task_hep_job_related (Task Job : eqType) jtR jtL pR pL (x y : Job) :
  (forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job (ar_decidable_eq Job) Task
        (ar_decidable_eq Task) jtL j)) ->
  SojJLFPRel Job pR pL ->
  ArBoolRel (@prosa.model.priority.definitions.another_task_hep_job Task Job jtR pR x y)
    (I.Prosa_Model_Priority_Definitions_another_task_hep_job Task (ar_decidable_eq Task)
      Job (ar_decidable_eq Job) jtL pL x y).
Proof.
  intros Hjt Hp. unfold prosa.model.priority.definitions.another_task_hep_job,
    I.Prosa_Model_Priority_Definitions_another_task_hep_job.
  exact (ar_bool_and_related _ _ _ _ (Hp x y)
    (soj_ne_observation_transport Task _ _ _ _ (Hjt x) (Hjt y))).
Qed.

Section ServiceOfJobs.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

  Lemma soj_service_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@prosa.behavior.service.service_at Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_service_at Job dJ PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.service_at.
    cbn [I.Prosa_Behavior_Service_service_at].
    exact (svc_service_in_related Job PStateR PStateL R j (schedR tR) (schedL tL) (Hsched tR tL Ht)).
  Qed.

  Lemma soj_service_during_related (j : Job) (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel (@prosa.behavior.service.service_during Job PStateR schedR j t1R t2R)
      (I.Prosa_Behavior_Service_service_during Job dJ PStateL schedL j t1L t2L).
  Proof.
    intros Ht1 Ht2.
    have Hsum := svc_interval_sum_related t1R t2R t1L t2L
      (fun t => @prosa.behavior.service.service_at Job PStateR schedR j t)
      (fun t => I.Prosa_Behavior_Service_service_at Job dJ PStateL schedL j t)
      Ht1 Ht2 (fun tR tL Ht => soj_service_at_related j tR tL Ht).
    change (SubNatRel
      (@prosa.behavior.service.service_during Job PStateR schedR j t1R t2R)
      (I.Prosa_Validation_ServiceInterface_serviceDuringProjection
        Job dJ PStateL schedL j t1L t2L)) in Hsum.
    exact Hsum.
  Qed.

  Section Sets.
    Variable PR : pred Job.
    Variable PL : Job -> I.Bool.
    Hypothesis HP : ArPredRel PR PL.
    Variable jobsR : seq Job.
    Variable jobsL : I.List Job.
    Hypothesis Hjobs : ArListRel jobsR jobsL.

    Theorem service_of_jobs_at_correspondence (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SubNatRel
        (@prosa.model.aggregate.service_of_jobs.service_of_jobs_at Job PStateR schedR PR jobsR tR)
        (I.Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs_at Job dJ PStateL schedL PL jobsL tL).
    Proof.
      intro Ht.
      unfold prosa.model.aggregate.service_of_jobs.service_of_jobs_at.
      cbn [I.Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs_at].
      exact (soj_sum_filter_related Job PR PL _ _ jobsR jobsL HP
        (fun j => soj_service_at_related j tR tL Ht) Hjobs).
    Qed.

    Theorem service_of_jobs_correspondence (t1R t2R : nat) (t1L t2L : Lean.Nat) :
      SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      SubNatRel
        (@prosa.model.aggregate.service_of_jobs.service_of_jobs Job PStateR schedR PR jobsR t1R t2R)
        (I.Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job dJ PStateL schedL PL jobsL t1L t2L).
    Proof.
      intros Ht1 Ht2.
      unfold prosa.model.aggregate.service_of_jobs.service_of_jobs.
      cbn [I.Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs].
      exact (soj_sum_filter_related Job PR PL _ _ jobsR jobsL HP
        (fun j => soj_service_during_related j t1R t2R t1L t2L Ht1 Ht2) Hjobs).
    Qed.
  End Sets.

  Theorem total_service_of_jobs_in_correspondence jobsR jobsL (Hjobs : ArListRel jobsR jobsL)
      (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel
      (@prosa.model.aggregate.service_of_jobs.total_service_of_jobs_in Job PStateR schedR jobsR t1R t2R)
      (I.Prosa_Model_Aggregate_ServiceOfJobs_total_service_of_jobs_in Job dJ PStateL schedL jobsL t1L t2L).
  Proof.
    intros Ht1 Ht2.
    unfold prosa.model.aggregate.service_of_jobs.total_service_of_jobs_in.
    cbn [I.Prosa_Model_Aggregate_ServiceOfJobs_total_service_of_jobs_in].
    refine (service_of_jobs_correspondence _ (fun _ => I.Bool_true) _
      jobsR jobsL Hjobs t1R t2R t1L t2L Ht1 Ht2).
    intro x. exact (@Lean.eq_refl _ _).
  Qed.

  Section Priority.
    Variable pR : prosa.model.priority.definitions.JLFP_policy Job.
    Variable pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
    Hypothesis Hp : SojJLFPRel Job pR pL.
    Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
    Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
    Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

    Theorem service_of_higher_or_equal_priority_jobs_correspondence jobsR jobsL
        (Hjobs : ArListRel jobsR jobsL) (j : Job) (t1R t2R : nat) (t1L t2L : Lean.Nat) :
      SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      SubNatRel
        (@prosa.model.aggregate.service_of_jobs.service_of_higher_or_equal_priority_jobs
          Job PStateR schedR pR jobsR j t1R t2R)
        (I.Prosa_Model_Aggregate_ServiceOfJobs_service_of_higher_or_equal_priority_jobs
          Job dJ PStateL schedL pL jobsL j t1L t2L).
    Proof.
      intros Ht1 Ht2.
      unfold prosa.model.aggregate.service_of_jobs.service_of_higher_or_equal_priority_jobs.
      cbn [I.Prosa_Model_Aggregate_ServiceOfJobs_service_of_higher_or_equal_priority_jobs].
      exact (service_of_jobs_correspondence _ _ (fun x => Hp x j) jobsR jobsL Hjobs
        t1R t2R t1L t2L Ht1 Ht2).
    Qed.

    Theorem service_of_other_hep_jobs_correspondence (j : Job) (t1R t2R : nat) (t1L t2L : Lean.Nat) :
      SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      SubNatRel
        (@prosa.model.aggregate.service_of_jobs.service_of_other_hep_jobs
          Job PStateR arrR schedR pR j t1R t2R)
        (I.Prosa_Model_Aggregate_ServiceOfJobs_service_of_other_hep_jobs
          Job dJ PStateL arrL schedL pL j t1L t2L).
    Proof.
      intros Ht1 Ht2.
      unfold prosa.model.aggregate.service_of_jobs.service_of_other_hep_jobs.
      cbn [I.Prosa_Model_Aggregate_ServiceOfJobs_service_of_other_hep_jobs].
      exact (service_of_jobs_correspondence _ _
        (fun x => soj_another_hep_job_related Job pR pL x j Hp) _ _
        (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ Ht1 Ht2)
        t1R t2R t1L t2L Ht1 Ht2).
    Qed.

    Theorem service_of_hep_jobs_correspondence (j : Job) (t1R t2R : nat) (t1L t2L : Lean.Nat) :
      SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      SubNatRel
        (@prosa.model.aggregate.service_of_jobs.service_of_hep_jobs
          Job PStateR arrR schedR pR j t1R t2R)
        (I.Prosa_Model_Aggregate_ServiceOfJobs_service_of_hep_jobs
          Job dJ PStateL arrL schedL pL j t1L t2L).
    Proof.
      intros Ht1 Ht2.
      unfold prosa.model.aggregate.service_of_jobs.service_of_hep_jobs.
      cbn [I.Prosa_Model_Aggregate_ServiceOfJobs_service_of_hep_jobs].
      exact (service_of_jobs_correspondence _ _ (fun x => Hp x j) _ _
        (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ Ht1 Ht2)
        t1R t2R t1L t2L Ht1 Ht2).
    Qed.

    Section Tasks.
      Context (Task : eqType).
      Let dT := ar_decidable_eq Task.
      Variable jtR : prosa.model.task.concept.JobTask Job Task.
      Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
      Hypothesis Hjt : forall j : Job,
        Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
          (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).

      Theorem service_of_other_task_hep_jobs_correspondence (j : Job)
          (t1R t2R : nat) (t1L t2L : Lean.Nat) :
        SubNatRel t1R t1L -> SubNatRel t2R t2L ->
        SubNatRel
          (@prosa.model.aggregate.service_of_jobs.service_of_other_task_hep_jobs
            Task Job jtR PStateR arrR schedR pR j t1R t2R)
          (I.Prosa_Model_Aggregate_ServiceOfJobs_service_of_other_task_hep_jobs
            Task dT Job dJ jtL PStateL arrL schedL pL j t1L t2L).
      Proof.
        intros Ht1 Ht2.
        unfold prosa.model.aggregate.service_of_jobs.service_of_other_task_hep_jobs.
        cbn [I.Prosa_Model_Aggregate_ServiceOfJobs_service_of_other_task_hep_jobs].
        exact (service_of_jobs_correspondence _ _
          (fun x => soj_another_task_hep_job_related Task Job jtR jtL pR pL x j Hjt Hp) _ _
          (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ Ht1 Ht2)
          t1R t2R t1L t2L Ht1 Ht2).
      Qed.
    End Tasks.
  End Priority.

  Section TaskService.
    Context (Task : eqType).
    Let dT := ar_decidable_eq Task.
    Variable jtR : prosa.model.task.concept.JobTask Job Task.
    Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
    Hypothesis Hjt : forall j : Job,
      Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).

    Theorem task_service_of_jobs_in_correspondence (tsk : Task) jobsR jobsL
        (Hjobs : ArListRel jobsR jobsL) (t1R t2R : nat) (t1L t2L : Lean.Nat) :
      SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      SubNatRel
        (@prosa.model.aggregate.service_of_jobs.task_service_of_jobs_in
          Task Job jtR PStateR schedR tsk jobsR t1R t2R)
        (I.Prosa_Model_Aggregate_ServiceOfJobs_task_service_of_jobs_in
          Task dT Job dJ jtL PStateL schedL tsk jobsL t1L t2L).
    Proof.
      intros Ht1 Ht2.
      unfold prosa.model.aggregate.service_of_jobs.task_service_of_jobs_in.
      cbn [I.Prosa_Model_Aggregate_ServiceOfJobs_task_service_of_jobs_in].
      exact (service_of_jobs_correspondence _ _
        (job_of_task_related Job Task jtR jtL Hjt tsk tsk (@Lean.eq_refl _ _)) jobsR jobsL Hjobs
        t1R t2R t1L t2L Ht1 Ht2).
    Qed.
  End TaskService.
End ServiceOfJobs.
