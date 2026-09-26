From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import SchedulabilitySemanticSource.
From prosa Require Import model.task.absolute_deadline.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSchedulability ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations.

Module I := ImportedSchedulability.
Module S := SchedulabilitySemanticSource.SchedulabilitySemanticSource.

(** Certificates for [analysis/definitions/schedulability.v].

    Source side: the extracted byte-identical definition blocks and the two
    extracted lemma statements, specialised at their leading inputs; target
    side: the compiled Lean declarations.  Inputs: [job_arrival] by
    [ArJobArrivalRel], [job_cost] by [SvcJobCostRel], [JobDeadline] and
    [TaskDeadline] pointwise by [SubNatRel], [job_task] by [Lean.eq],
    processor states by the accepted two-sided [SvcProcessorStateRel],
    schedules by [SvcScheduleRel] and arrival sequences by
    [ArArrivalSequenceRel] (both covered in both directions where they are
    quantified inside a statement).  Service, [completed_by] and
    [scheduled_at] are replayed from the accepted completion certificate.
    The task-derived absolute deadline of the source's global instance is
    related to the accepted Lean instance.  No source or target proof is
    used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma sch_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma sch_nat_input (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
Qed.

Lemma sch_logic_eq_to_lean_eq {A : Type} (x y : A) :
  Logic.eq x y -> Lean.eq x y.
Proof. intros []. exact (@Lean.eq_refl _ _). Qed.

Lemma sch_decide_eq_related (T : eqType) (x y : T) :
  ArBoolRel (x == y) (I.Decidable_decide (Lean.eq x y) (ar_decidable_eq T x y)).
Proof.
  apply sch_logic_eq_to_lean_eq.
  unfold ar_decidable_eq. case: eqP => H; reflexivity.
Qed.

Definition sch_arrival_sequence_to_source (Job : eqType)
    (arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job (ar_decidable_eq Job)) :
    prosa.behavior.arrival_sequence.arrival_sequence Job :=
  fun tR => ar_list_to_rocq (arrL (sub_nat_to_imported tR)).

Lemma sch_arrival_sequence_to_source_rel (Job : eqType) arrL :
  ArArrivalSequenceRel Job (sch_arrival_sequence_to_source Job arrL) arrL.
Proof.
  intros tR tL Ht. unfold ArListRel, sch_arrival_sequence_to_source.
  refine (sub_imported_eq_trans _ _ _ (ar_list_target_roundtrip _) _).
  exact (sub_imported_eq_congr arrL _ _ Ht).
Qed.

Lemma sch_forall_arrival_sequence (Job : eqType)
    (PR : prosa.behavior.arrival_sequence.arrival_sequence Job -> Prop)
    (PL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job (ar_decidable_eq Job) -> SProp) :
  (forall arrR arrL, ArArrivalSequenceRel Job arrR arrL -> PropSPropRel (PR arrR) (PL arrL)) ->
  PropSPropRel (forall arrR, PR arrR) (forall arrL, PL arrL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros HR arrL.
    exact (prop_to_sprop _ _ (H _ _ (sch_arrival_sequence_to_source_rel Job arrL)) (HR _)).
  - intro HL. apply strictly_inhabits. intro arrR.
    exact (sprop_to_prop _ _ (H _ _ (ar_arrival_sequence_canonical Job arrR)) (HL _)).
Qed.

Section Model.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.

  Section Sched.
    Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
    Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
    Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

    Lemma sch_scheduled_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SvcBoolRel (@prosa.behavior.service.scheduled_at Job PStateR schedR j tR)
        (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL schedL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.scheduled_at.
      cbn [I.Prosa_Behavior_Service_scheduled_at].
      exact (svc_scheduled_in_related Job PStateR PStateL R j (schedR tR) (schedL tL) (Hsched tR tL Ht)).
    Qed.

    Lemma sch_service_at_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SubNatRel (@prosa.behavior.service.service_at Job PStateR schedR j tR)
        (I.Prosa_Behavior_Service_service_at Job dJ PStateL schedL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.service_at.
      cbn [I.Prosa_Behavior_Service_service_at].
      exact (svc_service_in_related Job PStateR PStateL R j (schedR tR) (schedL tL) (Hsched tR tL Ht)).
    Qed.

    Lemma sch_service_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SubNatRel (@prosa.behavior.service.service Job PStateR schedR j tR)
        (I.Prosa_Behavior_Service_service Job dJ PStateL schedL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.service.
      cbn [I.Prosa_Behavior_Service_service].
      have Hsum := svc_interval_sum_related O tR Lean.Nat_zero tL
        (fun t => @prosa.behavior.service.service_at Job PStateR schedR j t)
        (fun t => I.Prosa_Behavior_Service_service_at Job dJ PStateL schedL j t)
        (sub_nat_rel_canonical O) Ht (fun xR xL Hx => sch_service_at_related j xR xL Hx).
      change (SubNatRel
        (@prosa.behavior.service.service_during Job PStateR schedR j O tR)
        (I.Prosa_Validation_ServiceInterface_serviceDuringProjection
          Job dJ PStateL schedL j Lean.Nat_zero tL)) in Hsum.
      exact Hsum.
    Qed.

    Lemma sch_completed_by_related (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      SvcBoolRel (@prosa.behavior.service.completed_by Job PStateR schedR costR j tR)
        (I.Prosa_Behavior_Service_completed_by Job dJ PStateL schedL costL j tL).
    Proof.
      intro Ht. unfold prosa.behavior.service.completed_by.
      cbn [I.Prosa_Behavior_Service_completed_by].
      exact (svc_decide_le_related _ _ _ _ (Hcost j) (sch_service_related j tR tL Ht)).
    Qed.

    Variable dlR : prosa.behavior.job.JobDeadline Job.
    Variable dlL : I.Prosa_Behavior_Job_JobDeadline Job dJ.
    Hypothesis Hdl : forall j : Job,
      SubNatRel (@prosa.behavior.job.job_deadline Job dlR j)
        (I.Prosa_Behavior_Job_JobDeadline_job_deadline Job dJ dlL j).

    Lemma sch_job_meets_deadline_related (j : Job) :
      SvcBoolRel (@prosa.behavior.service.job_meets_deadline Job PStateR schedR costR dlR j)
        (I.Prosa_Behavior_Service_job_meets_deadline Job dJ PStateL schedL costL dlL j).
    Proof.
      unfold prosa.behavior.service.job_meets_deadline.
      cbn [I.Prosa_Behavior_Service_job_meets_deadline].
      exact (sch_completed_by_related j _ _ (Hdl j)).
    Qed.

    Theorem all_deadlines_met_correspondence :
      PropSPropRel (@S.all_deadlines_met Job costR dlR PStateR schedR)
        (I.Prosa_Analysis_Definitions_Schedulability_all_deadlines_met Job dJ costL dlL PStateL schedL).
    Proof.
      unfold S.all_deadlines_met.
      cbn [I.Prosa_Analysis_Definitions_Schedulability_all_deadlines_met].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (sch_scheduled_at_related j tR tL Ht))|].
      exact (svc_bool_truth_correspondence _ _ (sch_job_meets_deadline_related j)).
    Qed.

    Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
    Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
    Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

    Theorem all_deadlines_of_arrivals_met_correspondence :
      PropSPropRel (@S.all_deadlines_of_arrivals_met Job costR dlR PStateR arrR schedR)
        (I.Prosa_Analysis_Definitions_Schedulability_all_deadlines_of_arrivals_met
          Job dJ costL dlL PStateL arrL schedL).
    Proof.
      unfold S.all_deadlines_of_arrivals_met.
      cbn [I.Prosa_Analysis_Definitions_Schedulability_all_deadlines_of_arrivals_met].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
      exact (svc_bool_truth_correspondence _ _ (sch_job_meets_deadline_related j)).
    Qed.

    Lemma sch_jobs_come_from_arrival_sequence_related :
      PropSPropRel (@prosa.behavior.ready.jobs_come_from_arrival_sequence Job PStateR schedR arrR)
        (I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job dJ PStateL schedL arrL).
    Proof.
      unfold prosa.behavior.ready.jobs_come_from_arrival_sequence.
      cbn [I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (sch_scheduled_at_related j tR tL Ht))|].
      exact (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    Qed.
  End Sched.

  (** *** Schedule cover *)

  Definition sch_schedule_to_target (schedR : @prosa.behavior.schedule.schedule Job PStateR) :
      I.Prosa_Behavior_Schedule_schedule Job dJ PStateL :=
    fun tL => svc_ps_state_to_target Job PStateR PStateL R (schedR (sub_nat_to_rocq tL)).

  Definition sch_schedule_to_source (schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL) :
      @prosa.behavior.schedule.schedule Job PStateR :=
    fun tR => svc_ps_state_to_source Job PStateR PStateL R (schedL (sub_nat_to_imported tR)).

  Lemma sch_schedule_to_target_rel schedR :
    SvcScheduleRel Job PStateR PStateL R schedR (sch_schedule_to_target schedR).
  Proof.
    intros tR tL Ht. unfold sch_schedule_to_target.
    rewrite (sch_nat_input _ _ Ht).
    exact (svc_ps_state_rel_canonical Job PStateR PStateL R (schedR tR)).
  Qed.

  Lemma sch_schedule_to_source_rel schedL :
    SvcScheduleRel Job PStateR PStateL R (sch_schedule_to_source schedL) schedL.
  Proof.
    intros tR tL Ht. unfold sch_schedule_to_source.
    exact (sch_lean_transport
      (fun sL => svc_ps_state_rel Job PStateR PStateL R
        (svc_ps_state_to_source Job PStateR PStateL R (schedL (sub_nat_to_imported tR))) sL)
      _ _ (sub_imported_eq_congr schedL _ _ Ht)
      (svc_ps_state_rel_surjective Job PStateR PStateL R _)).
  Qed.

  Lemma sch_forall_schedule
      (PR : @prosa.behavior.schedule.schedule Job PStateR -> Prop)
      (PL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL -> SProp) :
    (forall schedR schedL, SvcScheduleRel Job PStateR PStateL R schedR schedL ->
      PropSPropRel (PR schedR) (PL schedL)) ->
    PropSPropRel (forall schedR, PR schedR) (forall schedL, PL schedL).
  Proof.
    intro H. apply prop_sprop_rel_intro.
    - intros HR schedL. exact (prop_to_sprop _ _ (H _ _ (sch_schedule_to_source_rel schedL)) (HR _)).
    - intro HL. apply strictly_inhabits. intro schedR.
      exact (sprop_to_prop _ _ (H _ _ (sch_schedule_to_target_rel schedR)) (HL _)).
  Qed.

  Section Lemma2.
    Variable dlR : prosa.behavior.job.JobDeadline Job.
    Variable dlL : I.Prosa_Behavior_Job_JobDeadline Job dJ.
    Hypothesis Hdl : forall j : Job,
      SubNatRel (@prosa.behavior.job.job_deadline Job dlR j)
        (I.Prosa_Behavior_Job_JobDeadline_job_deadline Job dJ dlL j).

    Definition src_all_deadlines_met_in_valid_schedule : Prop :=
      ltac:(body_of (fun s : S.statement_all_deadlines_met_in_valid_schedule =>
        s Job costR dlR PStateR)).
    Definition tgt_all_deadlines_met_in_valid_schedule : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Definitions_Schedulability_all_deadlines_met_in_valid_schedule
        Job dJ costL dlL PStateL)).

    Theorem all_deadlines_met_in_valid_schedule_correspondence :
      PropSPropRel src_all_deadlines_met_in_valid_schedule tgt_all_deadlines_met_in_valid_schedule.
    Proof.
      apply sch_forall_arrival_sequence. intros arrR arrL Harr.
      apply sch_forall_schedule. intros schedR schedL Hsched.
      apply ar_imp_correspondence;
        [exact (sch_jobs_come_from_arrival_sequence_related schedR schedL Hsched arrR arrL Harr)|].
      apply ar_imp_correspondence;
        [exact (all_deadlines_of_arrivals_met_correspondence schedR schedL Hsched dlR dlL Hdl arrR arrL Harr)|].
      exact (all_deadlines_met_correspondence schedR schedL Hsched dlR dlL Hdl).
    Qed.
  End Lemma2.
End Model.

(** ** Task-level definitions and the schedulability lemma *)

Section Task.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Lemma sch_job_of_task_related (tsk : Task) (j : Job) :
    ArBoolRel (@prosa.model.task.concept.job_of_task Job Task jtR tsk j)
      (I.Prosa_Model_Task_Concept_job_of_task Job dJ Task dT jtL tsk j).
  Proof.
    unfold prosa.model.task.concept.job_of_task.
    cbn [I.Prosa_Model_Task_Concept_job_of_task].
    refine (sch_lean_transport
      (fun v => ArBoolRel (@prosa.model.task.concept.job_task Job Task jtR j == tsk)
        (I.Decidable_decide (Lean.eq v tsk) (dT v tsk))) _ _ (Hjt j) _).
    exact (sch_decide_eq_related Task _ tsk).
  Qed.

  Theorem task_response_time_bound_correspondence (tsk : Task) (rR : nat) (rL : Lean.Nat) :
    SubNatRel rR rL ->
    PropSPropRel (@S.task_response_time_bound Task Job jaR costR jtR PStateR arrR schedR tsk rR)
      (I.Prosa_Analysis_Definitions_Schedulability_task_response_time_bound
        Task dT Job dJ jaL costL jtL PStateL arrL schedL tsk rL).
  Proof.
    intro Hr. unfold S.task_response_time_bound.
    cbn [I.Prosa_Analysis_Definitions_Schedulability_task_response_time_bound].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (sch_job_of_task_related tsk j))|].
    apply svc_bool_truth_correspondence.
    unfold prosa.behavior.service.job_response_time_bound.
    cbn [I.Prosa_Behavior_Service_job_response_time_bound].
    exact (sch_completed_by_related Job costR costL Hcost PStateR PStateL R schedR schedL Hsched j _ _
      (svc_target_add_related _ _ _ _ (Hja j) Hr)).
  Qed.

  Variable dlR : prosa.behavior.job.JobDeadline Job.
  Variable dlL : I.Prosa_Behavior_Job_JobDeadline Job dJ.
  Hypothesis Hdl : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_deadline Job dlR j)
      (I.Prosa_Behavior_Job_JobDeadline_job_deadline Job dJ dlL j).

  Theorem schedulable_task_correspondence (tsk : Task) :
    PropSPropRel (@S.schedulable_task Task Job costR dlR jtR PStateR arrR schedR tsk)
      (I.Prosa_Analysis_Definitions_Schedulability_schedulable_task
        Task dT Job dJ costL dlL jtL PStateL arrL schedL tsk).
  Proof.
    unfold S.schedulable_task.
    cbn [I.Prosa_Analysis_Definitions_Schedulability_schedulable_task].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (sch_job_of_task_related tsk j))|].
    exact (svc_bool_truth_correspondence _ _
      (sch_job_meets_deadline_related Job costR costL Hcost PStateR PStateL R schedR schedL Hsched
        dlR dlL Hdl j)).
  Qed.
End Task.

Section Lemma1.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
  Variable tdR : prosa.model.task.concept.TaskDeadline Task.
  Variable tdL : I.Prosa_Model_Task_Concept_TaskDeadline Task dT.
  Hypothesis Htd : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_deadline Task tdR tsk)
      (I.Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task dT tdL tsk).
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

  (** The task-derived absolute deadline (the source's global instance) is
      related to the accepted Lean instance. *)
  Lemma sch_task_deadline_instance_related (j : Job) :
    SubNatRel
      (@prosa.behavior.job.job_deadline Job
        (@prosa.model.task.absolute_deadline.job_deadline_from_task_deadline Job Task tdR jaR jtR) j)
      (I.Prosa_Behavior_Job_JobDeadline_job_deadline Job dJ
        (I.Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline
          Job Task dJ dT tdL jaL jtL) j).
  Proof.
    cbn.
    exact (svc_target_add_related _ _ _ _ (Hja j)
      (sub_imported_eq_trans _ _ _ (Htd _)
        (sub_imported_eq_congr (I.Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task dT tdL)
          _ _ (Hjt j)))).
  Qed.

  Definition src_schedulability_from_response_time_bound (tsk : Task) (rR : nat) : Prop :=
    ltac:(body_of (fun s : S.statement_schedulability_from_response_time_bound =>
      s Task tdR Job jaR costR jtR PStateR arrR schedR tsk rR)).
  Definition tgt_schedulability_from_response_time_bound (tsk : Task) (rL : Lean.Nat) : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Definitions_Schedulability_schedulability_from_response_time_bound
      Task dT tdL Job dJ jaL costL jtL PStateL arrL schedL tsk rL)).

  Theorem schedulability_from_response_time_bound_correspondence (tsk : Task) rR rL :
    SubNatRel rR rL ->
    PropSPropRel (src_schedulability_from_response_time_bound tsk rR)
      (tgt_schedulability_from_response_time_bound tsk rL).
  Proof.
    intro Hr.
    unfold src_schedulability_from_response_time_bound, tgt_schedulability_from_response_time_bound.
    apply ar_imp_correspondence;
      [exact (task_response_time_bound_correspondence Task Job jaR jaL Hja costR costL Hcost jtR jtL Hjt
        PStateR PStateL R schedR schedL Hsched arrR arrL Harr tsk rR rL Hr)|].
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Hr (Htd tsk))|].
    exact (schedulable_task_correspondence Task Job costR costL Hcost jtR jtL Hjt
      PStateR PStateL R schedR schedL Hsched arrR arrL Harr _ _ sch_task_deadline_instance_related tsk).
  Qed.
End Lemma1.
