From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import ServiceInversionBusyPrefixSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRtaRsEdfLimitedPreemptive ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  ServiceInversionPredCorrespondence.

Module I := ImportedRtaRsEdfLimitedPreemptive.
Module S := ServiceInversionBusyPrefixSemanticSource.ServiceInversionBusyPrefixSemanticSource.
Module B := BusyIntervalClassicalSemanticSource.BusyIntervalClassicalSemanticSource.

(** Definition certificates for [analysis/definitions/service_inversion/busy_prefix.v].

    Source side: the extracted byte-identical definition blocks (the
    busy-interval and service-inversion-predicate imports bound to the
    accepted extracted sources); target side: the compiled Lean definitions.
    Inputs: [job_arrival] by [ArJobArrivalRel], [job_cost] by
    [SvcJobCostRel], [job_task] by [Lean.eq], processor states by the
    accepted two-sided [SvcProcessorStateRel], schedules by [SvcScheduleRel],
    arrival sequences by [ArArrivalSequenceRel], the JLFP policy pointwise on
    Booleans (its JLDP view through the source/target coercions reduces to
    it), the bound [B] on related Nats.  The predicates are closed by the
    accepted [ServiceInversionPredCorrespondence] re-instantiated at this
    artifact, the busy-interval prefix by the accepted busy-interval proof
    replayed here.  No source or target theorem is used. *)

Lemma sibp_false_correspondence : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - intro H. destruct H.
  - intro H. destruct H.
Qed.

Lemma sibp_not_correspondence (P : Prop) (PL : SProp) :
  PropSPropRel P PL -> PropSPropRel (~ P) (I.Not PL).
Proof.
  intro HP. unfold I.Not. apply ar_imp_correspondence; [exact HP|].
  exact sibp_false_correspondence.
Qed.

Section BusyPrefix.
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
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.
  Variable pR : prosa.model.priority.definitions.JLFP_policy Job.
  Variable pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
  Hypothesis Hp : forall x y : Job,
    ArBoolRel (@prosa.model.priority.definitions.hep_job Job pR x y)
      (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ pL x y).

  Let COMPLETED := pp_completed_by_related Job costR costL Hcost PStateR PStateL R schedR schedL Hsched.

  Lemma sibp_quiet_time_related (j : Job) (tR : nat) (tL : Lean.Nat) :
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

  Lemma sibp_busy_interval_prefix_related (j : Job) t1R t1L t2R t2L :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    PropSPropRel (@B.busy_interval_prefix Job jaR costR PStateR arrR schedR pR j t1R t2R)
      (I.Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix
        Job dJ jaL costL PStateL arrL schedL pL j t1L t2L).
  Proof.
    intros H1 H2. unfold B.busy_interval_prefix.
    cbn [I.Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix].
    apply ar_and_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ H1 H2)|].
    apply ar_and_correspondence; [exact (sibp_quiet_time_related j _ _ H1)|].
    apply ar_and_correspondence.
    - apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence.
      + exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
          (ar_decide_lt_related _ _ _ _ H1 Ht) (ar_decide_lt_related _ _ _ _ Ht H2))).
      + exact (sibp_not_correspondence _ _ (sibp_quiet_time_related j _ _ Ht)).
    - exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
        (ar_decide_le_related _ _ _ _ H1 (Hja j)) (ar_decide_lt_related _ _ _ _ (Hja j) H2))).
  Qed.

  Theorem service_inversion_of_job_is_bounded_by_correspondence (j : Job) BR BL :
    SvcNatFunRel BR BL ->
    PropSPropRel (@S.service_inversion_of_job_is_bounded_by Job jaR costR PStateR arrR schedR pR j BR)
      (I.Prosa_Analysis_Definitions_ServiceInversion_BusyPrefix_service_inversion_of_job_is_bounded_by
        Job dJ jaL costL PStateL arrL schedL pL j BL).
  Proof.
    intro HB. unfold S.service_inversion_of_job_is_bounded_by.
    cbn [I.Prosa_Analysis_Definitions_ServiceInversion_BusyPrefix_service_inversion_of_job_is_bounded_by].
    refine (pred_service_inversion_of_job_is_bounded_by_correspondence Job PStateR PStateL R
      schedR schedL Hsched arrR arrL Harr _ _ _ jaR jaL Hja _ _ _ j BR BL HB).
    - intros tR tL Ht x y. exact (Hp x y).
    - intros j' t1R t1L t2R t2L H1 H2. exact (sibp_busy_interval_prefix_related j' _ _ _ _ H1 H2).
  Qed.
End BusyPrefix.

Section TaskBound.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
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
  Variable pR : prosa.model.priority.definitions.JLFP_policy Job.
  Variable pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
  Hypothesis Hp : forall x y : Job,
    ArBoolRel (@prosa.model.priority.definitions.hep_job Job pR x y)
      (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ pL x y).

  Theorem service_inversion_is_bounded_by_correspondence (tsk : Task) BR BL :
    SvcNatFunRel BR BL ->
    PropSPropRel
      (@S.service_inversion_is_bounded_by Task Job jtR jaR costR PStateR arrR schedR pR tsk BR)
      (I.Prosa_Analysis_Definitions_ServiceInversion_BusyPrefix_service_inversion_is_bounded_by
        Task dT Job dJ jtL jaL costL PStateL arrL schedL pL tsk BL).
  Proof.
    intro HB. unfold S.service_inversion_is_bounded_by.
    cbn [I.Prosa_Analysis_Definitions_ServiceInversion_BusyPrefix_service_inversion_is_bounded_by].
    refine (pred_service_inversion_is_bounded_by_correspondence Task Job jtR jtL Hjt jaR jaL Hja
      costR costL Hcost PStateR PStateL R schedR schedL Hsched arrR arrL Harr _ _ _ _ _ _ tsk BR BL HB).
    - intros tR tL Ht x y. exact (Hp x y).
    - intros j' t1R t1L t2R t2L H1 H2.
      exact (sibp_busy_interval_prefix_related Job jaR jaL Hja costR costL Hcost PStateR PStateL R
        arrR arrL Harr schedR schedL Hsched pR pL Hp j' _ _ _ _ H1 H2).
  Qed.
End TaskBound.
