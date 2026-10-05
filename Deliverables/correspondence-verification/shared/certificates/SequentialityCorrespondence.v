From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import model.task.sequentiality.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSequentiality ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations.

Module I := ImportedSequentiality.

(** Definition certificates for [model/task/sequentiality.v]: for related
    inputs (processor state with the two-sided [SvcProcessorStateRel],
    schedule, arrival sequence, [job_task], [job_arrival], [job_cost]) the
    source definitions and the compiled Lean definitions are related. *)

(** MathComp [all] versus Lean [List.all]. *)
Lemma sq_all_canonical (T : Type) (pR : T -> bool) (pL : T -> I.Bool) :
  (forall x, ArBoolRel (pR x) (pL x)) ->
  forall xs : seq T, ArBoolRel (all pR xs) (I.List_all T (ar_list_to_imported xs) pL).
Proof.
  intros Hp xs. induction xs as [|x xs IH].
  - exact (@Lean.eq_refl _ _).
  - exact (ar_bool_and_related _ _ _ _ (Hp x) IH).
Qed.

Lemma sq_all_related (T : Type) (pR : T -> bool) (pL : T -> I.Bool) xsR xsL :
  (forall x, ArBoolRel (pR x) (pL x)) -> ArListRel xsR xsL ->
  ArBoolRel (all pR xsR) (I.List_all T xsL pL).
Proof.
  intros Hp Hxs.
  refine (ari_lean_transport (fun l => ArBoolRel (all pR xsR) (I.List_all T l pL)) _ _ Hxs _).
  exact (sq_all_canonical T pR pL Hp xsR).
Qed.

Section Sequentiality.
  Context (Job Task : eqType).
  Let dJ := ar_decidable_eq Job.
  Let dT := ar_decidable_eq Task.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

  (** Service operations (same proofs as the accepted readiness/basic and
      facts/behavior/arrivals certificates) at this artifact's identity. *)
  Lemma sq_service_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@prosa.behavior.service.service_at Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_service_at Job dJ PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.service_at.
    cbn [I.Prosa_Behavior_Service_service_at].
    exact (svc_service_in_related Job PStateR PStateL R j (schedR tR) (schedL tL) (Hsched tR tL Ht)).
  Qed.

  Lemma sq_service_during_related (j : Job) (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel (@prosa.behavior.service.service_during Job PStateR schedR j t1R t2R)
      (I.Prosa_Behavior_Service_service_during Job dJ PStateL schedL j t1L t2L).
  Proof.
    intros Ht1 Ht2.
    have Hsum := svc_interval_sum_related t1R t2R t1L t2L
      (fun t => @prosa.behavior.service.service_at Job PStateR schedR j t)
      (fun t => I.Prosa_Behavior_Service_service_at Job dJ PStateL schedL j t)
      Ht1 Ht2 (fun tR tL Ht => sq_service_at_related j tR tL Ht).
    change (SubNatRel
      (@prosa.behavior.service.service_during Job PStateR schedR j t1R t2R)
      (I.Prosa_Validation_ServiceInterface_serviceDuringProjection
        Job dJ PStateL schedL j t1L t2L)) in Hsum.
    exact Hsum.
  Qed.

  Lemma sq_service_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@prosa.behavior.service.service Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_service Job dJ PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.service.
    cbn [I.Prosa_Behavior_Service_service].
    exact (sq_service_during_related j O tR Lean.Nat_zero tL (sub_nat_rel_canonical O) Ht).
  Qed.

  Lemma sq_completed_by_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.service.completed_by Job PStateR schedR costR j tR)
      (I.Prosa_Behavior_Service_completed_by Job dJ PStateL schedL costL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.completed_by.
    cbn [I.Prosa_Behavior_Service_completed_by].
    exact (svc_decide_le_related _ _ _ _ (Hcost j) (sq_service_related j tR tL Ht)).
  Qed.

  Lemma sq_scheduled_at_related (j : Job) tR tL :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.service.scheduled_at Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL schedL j tL).
  Proof. intro Ht. exact (svc_scheduled_in_related Job PStateR PStateL R j _ _ (Hsched tR tL Ht)). Qed.

  Lemma sq_same_task_related (j1 j2 : Job) :
    ArBoolRel (@prosa.model.task.concept.same_task Job Task jtR j1 j2)
      (I.Prosa_Model_Task_Concept_same_task Job dJ Task dT jtL j1 j2).
  Proof.
    unfold prosa.model.task.concept.same_task.
    cbn [I.Prosa_Model_Task_Concept_same_task].
    refine (ari_lean_transport (fun v => ArBoolRel _
      (I.Decidable_decide (Lean.eq v (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j2))
        (dT v (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j2)))) _ _ (Hjt j1) _).
    refine (ari_lean_transport (fun v => ArBoolRel _
      (I.Decidable_decide (Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j1) v)
        (dT (@prosa.model.task.concept.job_task Job Task jtR j1) v))) _ _ (Hjt j2) _).
    exact (ari_decide_eq_related Task _ _).
  Qed.

  Theorem sequential_tasks_correspondence :
    PropSPropRel
      (@prosa.model.task.sequentiality.sequential_tasks Job Task jtR jaR costR PStateR arrR schedR)
      (I.Prosa_Model_Task_Sequentiality_sequential_tasks Job dJ Task dT jtL jaL costL PStateL arrL schedL).
  Proof.
    unfold prosa.model.task.sequentiality.sequential_tasks.
    cbn [I.Prosa_Model_Task_Sequentiality_sequential_tasks].
    apply ar_forall_identity_correspondence => j1.
    apply ar_forall_identity_correspondence => j2.
    apply ar_forall_nat_correspondence => tR tL Ht.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j1 Harr)|].
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j2 Harr)|].
    apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (sq_same_task_related j1 j2))|].
    apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ (Hja j1) (Hja j2))|].
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (sq_scheduled_at_related j2 tR tL Ht))|].
    exact (ar_bool_truth_correspondence _ _ (sq_completed_by_related j1 tR tL Ht)).
  Qed.

  Theorem prior_jobs_complete_correspondence (j : Job) tR tL :
    SubNatRel tR tL ->
    ArBoolRel
      (@prosa.model.task.sequentiality.prior_jobs_complete Job Task jtR jaR costR PStateR arrR schedR j tR)
      (I.Prosa_Model_Task_Sequentiality_prior_jobs_complete Job dJ Task dT jtL jaL costL PStateL arrL schedL j tL).
  Proof.
    intro Ht.
    unfold prosa.model.task.sequentiality.prior_jobs_complete.
    cbn [I.Prosa_Model_Task_Sequentiality_prior_jobs_complete].
    apply sq_all_related.
    - intro x. exact (sq_completed_by_related x tR tL Ht).
    - exact (task_arrivals_before_correspondence Job Task jtR jtL Hjt arrR arrL Harr
        _ _ _ _ (Hjt j) (Hja j)).
  Qed.
End Sequentiality.
