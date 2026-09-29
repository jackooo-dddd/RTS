From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import WorkloadBoundedSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRtaRsEdfFullyPreemptive ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  WorkloadCorrespondence.

Module I := ImportedRtaRsEdfFullyPreemptive.
Module S := WorkloadBoundedSemanticSource.WorkloadBoundedSemanticSource.
Module B := BusyIntervalClassicalSemanticSource.BusyIntervalClassicalSemanticSource.

(** Definition certificate for [analysis/definitions/workload/bounded.v].

    Source side: the extracted byte-identical definition block (the
    busy-interval import bound to the accepted extracted busy-interval
    source); target side: the compiled Lean definition.  Inputs:
    [job_cost] by [SvcJobCostRel], [job_arrival] by [ArJobArrivalRel],
    [job_task] by [Lean.eq], processor states by the accepted two-sided
    [SvcProcessorStateRel], schedules by [SvcScheduleRel], arrival sequences
    by [ArArrivalSequenceRel], the JLFP policy pointwise on Booleans, the
    bound [B] on related Nats.  [workload_of_jobs] and [arrivals_between] are
    closed by the accepted workload and arrival-sequence certificates;
    [quiet_time], [another_task_hep_job] and [job_of_task] replay the
    accepted busy-interval, workload-facts and schedulability proofs.  No
    source or target theorem is used. *)

Lemma wlb_logic_eq_to_lean_eq {A : Type} (x y : A) :
  Logic.eq x y -> Lean.eq x y.
Proof. intros []. exact (@Lean.eq_refl _ _). Qed.

Lemma wlb_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma wlb_decide_eq_related (T : eqType) (x y : T) :
  ArBoolRel (x == y) (I.Decidable_decide (Lean.eq x y) (ar_decidable_eq T x y)).
Proof.
  apply wlb_logic_eq_to_lean_eq.
  unfold ar_decidable_eq. case: eqP => H; reflexivity.
Qed.

Section Bounded.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable pR : prosa.model.priority.definitions.JLFP_policy Job.
  Variable pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
  Hypothesis Hp : forall x y : Job,
    ArBoolRel (@prosa.model.priority.definitions.hep_job Job pR x y)
      (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ pL x y).
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.
  Variable tsk : Task.
  Variable BR : nat -> nat -> nat.
  Variable BL : Lean.Nat -> Lean.Nat -> Lean.Nat.
  Hypothesis HB : forall aR aL dR dL, SubNatRel aR aL -> SubNatRel dR dL ->
    SubNatRel (BR aR dR) (BL aL dL).

  Let COMPLETED := pp_completed_by_related Job costR costL Hcost PStateR PStateL R schedR schedL Hsched.

  Lemma wlb_quiet_time_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    PropSPropRel (@B.quiet_time Job jaR costR PStateR arrR schedR pR j tR)
      (I.Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time
        Job dJ jaL costL PStateL arrL schedL pL j tL).
  Proof.
    intro Ht. unfold B.quiet_time.
    cbn [I.Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time].
    apply ar_forall_identity_correspondence. intro j_hp.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j_hp Harr)|].
    apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hp j_hp j))|].
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _
        (arrived_before_correspondence_certificate Job jaR jaL j_hp Hja tR tL Ht))|].
    exact (ar_bool_truth_correspondence _ _ (COMPLETED j_hp tR tL Ht)).
  Qed.

  Lemma wlb_job_of_task_related (j : Job) :
    ArBoolRel (@prosa.model.task.concept.job_of_task Job Task jtR tsk j)
      (I.Prosa_Model_Task_Concept_job_of_task Job dJ Task dT jtL tsk j).
  Proof.
    unfold prosa.model.task.concept.job_of_task.
    cbn [I.Prosa_Model_Task_Concept_job_of_task].
    refine (wlb_lean_transport
      (fun v => ArBoolRel (@prosa.model.task.concept.job_task Job Task jtR j == tsk)
        (I.Decidable_decide (Lean.eq v tsk) (dT v tsk))) _ _ (Hjt j) _).
    exact (wlb_decide_eq_related Task _ tsk).
  Qed.

  Lemma wlb_another_task_hep_job_related (x y : Job) :
    ArBoolRel (@prosa.model.priority.definitions.another_task_hep_job Task Job jtR pR x y)
      (I.Prosa_Model_Priority_Definitions_another_task_hep_job Task dT Job dJ jtL pL x y).
  Proof.
    unfold prosa.model.priority.definitions.another_task_hep_job.
    cbn [I.Prosa_Model_Priority_Definitions_another_task_hep_job].
    apply (ar_bool_and_related _ _ _ _ (Hp x y)).
    exact (wlb_lean_transport
      (fun a => ArBoolRel (@prosa.model.task.concept.job_task Job Task jtR x !=
           @prosa.model.task.concept.job_task Job Task jtR y)
         (I.Decidable_decide (I.Ne Task a (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL y))
            (I.instDecidableNot (Lean.eq a (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL y))
               (ar_decidable_eq Task a (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL y)))))
      _ _ (Hjt x)
      (wlb_lean_transport
        (fun b => ArBoolRel (@prosa.model.task.concept.job_task Job Task jtR x !=
             @prosa.model.task.concept.job_task Job Task jtR y)
           (I.Decidable_decide (I.Ne Task (@prosa.model.task.concept.job_task Job Task jtR x) b)
              (I.instDecidableNot (Lean.eq (@prosa.model.task.concept.job_task Job Task jtR x) b)
                 (ar_decidable_eq Task (@prosa.model.task.concept.job_task Job Task jtR x) b))))
        _ _ (Hjt y) (wl_ne_observation Task _ _))).
  Qed.

  Theorem athep_workload_is_bounded_correspondence :
    PropSPropRel
      (@S.athep_workload_is_bounded Task Job costR jaR jtR PStateR pR arrR schedR tsk BR)
      (I.Prosa_Analysis_Definitions_Workload_Bounded_athep_workload_is_bounded
        Task dT Job dJ costL jaL jtL PStateL pL arrL schedL tsk BL).
  Proof.
    unfold S.athep_workload_is_bounded.
    cbn [I.Prosa_Analysis_Definitions_Workload_Bounded_athep_workload_is_bounded].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_forall_nat_correspondence. intros dR dL Hd.
    apply ar_imp_correspondence.
    { unfold prosa.model.job.properties.job_cost_positive.
      cbn [I.Prosa_Model_Job_Properties_job_cost_positive].
      exact (ar_bool_truth_correspondence _ _
        (svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O) (Hcost j))). }
    apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (wlb_job_of_task_related j))|].
    apply ar_imp_correspondence; [exact (wlb_quiet_time_related j _ _ Ht1)|].
    exact (sub_nat_le_correspondence _ _ _ _
      (workload_of_jobs_correspondence Job costR costL Hcost _ _
        (fun x => wlb_another_task_hep_job_related x j) _ _
        (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ Ht1
          (svc_target_add_related _ _ _ _ Ht1 Hd)))
      (HB _ _ _ _ (svc_target_sub_related _ _ _ _ (Hja j) Ht1) Hd)).
  Qed.
End Bounded.
