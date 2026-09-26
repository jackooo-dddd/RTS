From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import FactsTaskScheduleSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsTaskSchedule ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PStateCover.

Module I := ImportedFactsTaskSchedule.
Module S := FactsTaskScheduleSemanticSource.FactsTaskScheduleSemanticSource.

(** Statement correspondences for [analysis/facts/model/task_schedule.v].

    Source side: the extracted statement [S.statement_X] specialised at its
    leading inputs (task and job types, [JobTask], [JobArrival] when present,
    arrival sequence); target side: the type of the imported Lean theorem at
    related inputs ([JobTask] by [Lean.eq] on [job_task], [ArJobArrivalRel],
    [ArArrivalSequenceRel]).  Processor models, schedules, tasks, jobs and
    instants bound later are covered in both directions through the accepted
    [PStateCover] layer ([IsjPSRel]).  The task-level schedule predicates are
    related over any per-instant [scheduled_at]/[service_at] correspondence.
    No source or target theorem is used. *)

(** ** Task membership and list emptiness *)

Definition FtsJobTaskRel (Job Task : eqType)
    (jtR : prosa.model.task.concept.JobTask Job Task)
    (jtL : I.Prosa_Model_Task_Concept_JobTask Job (ar_decidable_eq Job) Task (ar_decidable_eq Task)) : SProp :=
  forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job (ar_decidable_eq Job) Task (ar_decidable_eq Task) jtL j).

Lemma fts_decide_eq_related (Task : eqType) (x y : Task) :
  SvcBoolRel (x == y) (I.Decidable_decide (Lean.eq x y) (ar_decidable_eq Task x y)).
Proof.
  apply ar_decide_bool_correspondence.
  apply prop_sprop_rel_intro.
  - move/eqP => Heq. exact (coq_eq_to_imported_eq _ _ Heq).
  - intro Heq. apply strictly_inhabits. apply/eqP.
    exact (imported_eq_to_coq_eq _ _ Heq).
Qed.

Lemma fts_bool_eq_correspondence (bR cR : bool) (bL cL : I.Bool) :
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

Lemma fts_nil_eq_isEmpty_related {T : eqType} (xsR : seq T) (xsL : I.List T) :
  ArListRel xsR xsL -> SvcBoolRel (xsR == [::]) (I.List_isEmpty T xsL).
Proof.
  intro Hxs. unfold SvcBoolRel, ArListRel in *.
  refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_congr (I.List_isEmpty T) _ _ Hxs)).
  destruct xsR as [|x xs].
  - exact (sub_imported_eq_sym _ _ (I.Prosa_Validation_ScheduledInterface_production_isEmpty_nil T)).
  - exact (sub_imported_eq_sym _ _
      (I.Prosa_Validation_ScheduledInterface_production_isEmpty_cons T x (ar_list_to_imported xs))).
Qed.

(** ** Task-level schedule predicates over per-instant correspondences *)

Section TaskOps.
  Context (Task Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let dT := ar_decidable_eq Task.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : FtsJobTaskRel Job Task jtR jtL.

  Lemma fts_job_of_task_related (tsk : Task) (j : Job) :
    SvcBoolRel (@prosa.model.task.concept.job_of_task Job Task jtR tsk j)
      (I.Prosa_Model_Task_Concept_job_of_task Job dJ Task dT jtL tsk j).
  Proof.
    unfold prosa.model.task.concept.job_of_task.
    cbn [I.Prosa_Model_Task_Concept_job_of_task].
    exact (isj_lean_transport
      (fun x => SvcBoolRel (@prosa.model.task.concept.job_task Job Task jtR j == tsk)
         (I.Decidable_decide (Lean.eq x tsk) (ar_decidable_eq Task x tsk)))
      _ _ (Hjt j) (fts_decide_eq_related Task _ tsk)).
  Qed.

  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Hypothesis Hsa : forall (j : Job) (tR : nat) (tL : Lean.Nat), SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.service.scheduled_at Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_scheduled_at Job dJ PStateL schedL j tL).
  Hypothesis Hse : forall (j : Job) (tR : nat) (tL : Lean.Nat), SubNatRel tR tL ->
    SubNatRel (@prosa.behavior.service.service_at Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_service_at Job dJ PStateL schedL j tL).
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.
  Variable tsk : Task.

  Lemma fts_receives_service_related (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.behavior.service.receives_service_at Job PStateR schedR j tR)
      (I.Prosa_Behavior_Service_receives_service_at Job dJ PStateL schedL j tL).
  Proof.
    intro Ht. unfold prosa.behavior.service.receives_service_at.
    cbn [I.Prosa_Behavior_Service_receives_service_at].
    exact (svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O) (Hse j tR tL Ht)).
  Qed.

  Lemma fts_scheduled_jobs_of_task_related (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    ArListRel
      (@prosa.analysis.definitions.task_schedule.scheduled_jobs_of_task_at Task Job jtR arrR PStateR schedR tsk tR)
      (I.Prosa_Analysis_Definitions_TaskSchedule_scheduled_jobs_of_task_at Task dT Job dJ jtL PStateL
        arrL schedL tsk tL).
  Proof.
    intro Ht.
    unfold prosa.analysis.definitions.task_schedule.scheduled_jobs_of_task_at.
    cbn [I.Prosa_Analysis_Definitions_TaskSchedule_scheduled_jobs_of_task_at].
    apply ar_filter_related.
    - intro j. exact (fts_job_of_task_related tsk j).
    - exact (isj_scheduled_jobs_at_related Job PStateR PStateL schedR schedL Hsa arrR arrL Harr tR tL Ht).
  Qed.

  Lemma fts_task_scheduled_at_related (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel
      (@prosa.analysis.definitions.task_schedule.task_scheduled_at Task Job jtR arrR PStateR schedR tsk tR)
      (I.Prosa_Analysis_Definitions_TaskSchedule_task_scheduled_at Task dT Job dJ jtL PStateL
        arrL schedL tsk tL).
  Proof.
    intro Ht.
    unfold prosa.analysis.definitions.task_schedule.task_scheduled_at.
    cbn [I.Prosa_Analysis_Definitions_TaskSchedule_task_scheduled_at].
    exact (svc_bool_not_related _ _ (fts_nil_eq_isEmpty_related _ _ (fts_scheduled_jobs_of_task_related tR tL Ht))).
  Qed.

  Lemma fts_served_jobs_of_task_related (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    ArListRel
      (@prosa.analysis.definitions.task_schedule.served_jobs_of_task_at Task Job jtR arrR PStateR schedR tsk tR)
      (I.Prosa_Analysis_Definitions_TaskSchedule_served_jobs_of_task_at Task dT Job dJ jtL PStateL
        arrL schedL tsk tL).
  Proof.
    intro Ht.
    unfold prosa.analysis.definitions.task_schedule.served_jobs_of_task_at.
    cbn [I.Prosa_Analysis_Definitions_TaskSchedule_served_jobs_of_task_at].
    apply ar_filter_related.
    - intro j. exact (fts_receives_service_related j tR tL Ht).
    - exact (fts_scheduled_jobs_of_task_related tR tL Ht).
  Qed.

  Lemma fts_task_served_at_related (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel
      (@prosa.analysis.definitions.task_schedule.task_served_at Task Job jtR arrR PStateR schedR tsk tR)
      (I.Prosa_Analysis_Definitions_TaskSchedule_task_served_at Task dT Job dJ jtL PStateL
        arrL schedL tsk tL).
  Proof.
    intro Ht.
    unfold prosa.analysis.definitions.task_schedule.task_served_at.
    cbn [I.Prosa_Analysis_Definitions_TaskSchedule_task_served_at].
    exact (svc_bool_not_related _ _ (fts_nil_eq_isEmpty_related _ _ (fts_served_jobs_of_task_related tR tL Ht))).
  Qed.
End TaskOps.

(** ** Supply for processor models related by [IsjPSRel] *)

Section PSupply.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Variable PR : prosa.behavior.schedule.ProcessorState Job.
  Variable PL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable X : IsjPSRel Job PR PL.

  Lemma fts_psr_supply_at_related schedR schedL (Hs : IsjPSchedRel Job PR PL X schedR schedL)
      (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SubNatRel (@prosa.model.processor.supply.supply_at Job PR schedR tR)
      (I.Prosa_Model_Processor_Supply_supply_at Job dJ PL schedL tL).
  Proof.
    intro Ht. unfold prosa.model.processor.supply.supply_at.
    cbn [I.Prosa_Model_Processor_Supply_supply_at].
    exact (isj_lean_transport
      (fun sL => SubNatRel (@prosa.behavior.schedule.supply_in Job PR (schedR tR))
         (I.Prosa_Behavior_Schedule_ProcessorState_supply_in Job dJ PL sL))
      _ _ (Hs tR tL Ht) (isj_sup_in_rel Job PR PL X (schedR tR))).
  Qed.

  Lemma fts_psr_has_supply_related schedR schedL (Hs : IsjPSchedRel Job PR PL X schedR schedL)
      (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    SvcBoolRel (@prosa.model.processor.supply.has_supply Job PR schedR tR)
      (I.Prosa_Model_Processor_Supply_has_supply Job dJ PL schedL tL).
  Proof.
    intro Ht. unfold prosa.model.processor.supply.has_supply.
    cbn [I.Prosa_Model_Processor_Supply_has_supply].
    exact (svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O)
      (fts_psr_supply_at_related schedR schedL Hs tR tL Ht)).
  Qed.

  Lemma fts_psr_fully_consuming_related :
    PropSPropRel (@prosa.model.processor.platform_properties.fully_consuming_proc_model Job PR)
      (I.Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model Job dJ PL).
  Proof.
    unfold prosa.model.processor.platform_properties.fully_consuming_proc_model.
    cbn [I.Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model].
    apply ar_forall_identity_correspondence. intro j.
    apply (isj_forall_cover_sprop _ _ (IsjPSchedRel Job PR PL X)
      (isj_psr_sched_to_target Job PR PL X) (isj_psr_sched_to_source Job PR PL X)
      (isj_psr_sched_to_target_rel Job PR PL X) (isj_psr_sched_to_source_rel Job PR PL X)).
    intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence;
      [exact (svc_bool_truth_correspondence _ _ (isj_psr_scheduled_at_related Job PR PL X sR sL Hs j _ _ Ht))|].
    exact (sub_nat_eq_correspondence _ _ _ _ (isj_psr_service_at_related Job PR PL X sR sL Hs j _ _ Ht)
      (fts_psr_supply_at_related sR sL Hs _ _ Ht)).
  Qed.
End PSupply.

(** ** Statements *)

Section Statements.
  Context (Task Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let dT := ar_decidable_eq Task.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : FtsJobTaskRel Job Task jtR jtL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Let cover_sched PR PL (X : IsjPSRel Job PR PL) :=
    isj_forall_cover_sprop _ _ (IsjPSchedRel Job PR PL X)
      (isj_psr_sched_to_target Job PR PL X) (isj_psr_sched_to_source Job PR PL X)
      (isj_psr_sched_to_target_rel Job PR PL X) (isj_psr_sched_to_source_rel Job PR PL X).

  Definition src_task_served_task_scheduled : Prop :=
    ltac:(body_of (fun s : S.statement_task_served_task_scheduled => s Task Job jtR arrR)).
  Definition tgt_task_served_task_scheduled : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskSchedule_task_served_task_scheduled
      Task dT Job dJ jtL arrL)).
  Theorem task_served_task_scheduled_correspondence :
    PropSPropRel src_task_served_task_scheduled tgt_task_served_task_scheduled.
  Proof.
    apply (isj_cover_pstate Job). intros PR PL X.
    apply (cover_sched PR PL X). intros sR sL Hs.
    have HSA := isj_psr_scheduled_at_related Job PR PL X sR sL Hs.
    have HSE := isj_psr_service_at_related Job PR PL X sR sL Hs.
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence;
      [exact (svc_bool_truth_correspondence _ _
        (fts_task_served_at_related Task Job jtR jtL Hjt PR PL sR sL HSA HSE arrR arrL Harr tsk tR tL Ht))|].
    exact (svc_bool_truth_correspondence _ _
      (fts_task_scheduled_at_related Task Job jtR jtL Hjt PR PL sR sL HSA arrR arrL Harr tsk tR tL Ht)).
  Qed.

  Section WithArrival.
    Variable jaR : prosa.behavior.job.JobArrival Job.
    Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
    Hypothesis Hja : ArJobArrivalRel Job jaR jaL.

    Let valid_rel := valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr.

    Definition src_task_served_eq_task_scheduled : Prop :=
      ltac:(body_of (fun s : S.statement_task_served_eq_task_scheduled => s Task Job jtR jaR arrR)).
    Definition tgt_task_served_eq_task_scheduled : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskSchedule_task_served_eq_task_scheduled
        Task dT Job dJ jtL jaL arrL)).
    Theorem task_served_eq_task_scheduled_correspondence :
      PropSPropRel src_task_served_eq_task_scheduled tgt_task_served_eq_task_scheduled.
    Proof.
      apply ar_imp_correspondence; [exact valid_rel|].
      apply (isj_cover_pstate Job). intros PR PL X.
      apply (cover_sched PR PL X). intros sR sL Hs.
      have HSA := isj_psr_scheduled_at_related Job PR PL X sR sL Hs.
      have HSE := isj_psr_service_at_related Job PR PL X sR sL Hs.
      apply ar_imp_correspondence; [exact (isj_jobs_come_from_related Job PR PL sR sL HSA arrR arrL Harr)|].
      apply ar_imp_correspondence; [exact (isj_jobs_must_arrive_related Job PR PL sR sL HSA jaR jaL Hja)|].
      apply ar_forall_identity_correspondence. intro tsk.
      apply ar_imp_correspondence; [exact (isj_psr_ideal_progress_related Job PR PL X)|].
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      exact (fts_bool_eq_correspondence _ _ _ _
        (fts_task_served_at_related Task Job jtR jtL Hjt PR PL sR sL HSA HSE arrR arrL Harr tsk tR tL Ht)
        (fts_task_scheduled_at_related Task Job jtR jtL Hjt PR PL sR sL HSA arrR arrL Harr tsk tR tL Ht)).
    Qed.

    Definition src_no_task_scheduled_when_idle : Prop :=
      ltac:(body_of (fun s : S.statement_no_task_scheduled_when_idle => s Task Job jtR jaR arrR)).
    Definition tgt_no_task_scheduled_when_idle : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskSchedule_no_task_scheduled_when_idle
        Task dT Job dJ jtL jaL arrL)).
    Theorem no_task_scheduled_when_idle_correspondence : PropSPropRel src_no_task_scheduled_when_idle tgt_no_task_scheduled_when_idle.
    Proof.
      apply ar_imp_correspondence; [exact valid_rel|].
      apply (isj_cover_pstate Job). intros PR PL X.
      apply (cover_sched PR PL X). intros sR sL Hs.
      have HSA := isj_psr_scheduled_at_related Job PR PL X sR sL Hs.
      have HSE := isj_psr_service_at_related Job PR PL X sR sL Hs.
      apply ar_imp_correspondence; [exact (isj_jobs_come_from_related Job PR PL sR sL HSA arrR arrL Harr)|].
      apply ar_imp_correspondence; [exact (isj_jobs_must_arrive_related Job PR PL sR sL HSA jaR jaL Hja)|].
      apply ar_forall_identity_correspondence. intro tsk.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (isj_is_idle_related Job PR PL sR sL HSA arrR arrL Harr tR tL Ht))|].
      exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (fts_task_scheduled_at_related Task Job jtR jtL Hjt PR PL sR sL HSA arrR arrL Harr tsk tR tL Ht))).
    Qed.

    Definition src_no_task_served_when_idle : Prop :=
      ltac:(body_of (fun s : S.statement_no_task_served_when_idle => s Task Job jtR jaR arrR)).
    Definition tgt_no_task_served_when_idle : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskSchedule_no_task_served_when_idle
        Task dT Job dJ jtL jaL arrL)).
    Theorem no_task_served_when_idle_correspondence : PropSPropRel src_no_task_served_when_idle tgt_no_task_served_when_idle.
    Proof.
      apply ar_imp_correspondence; [exact valid_rel|].
      apply (isj_cover_pstate Job). intros PR PL X.
      apply (cover_sched PR PL X). intros sR sL Hs.
      have HSA := isj_psr_scheduled_at_related Job PR PL X sR sL Hs.
      have HSE := isj_psr_service_at_related Job PR PL X sR sL Hs.
      apply ar_imp_correspondence; [exact (isj_jobs_come_from_related Job PR PL sR sL HSA arrR arrL Harr)|].
      apply ar_imp_correspondence; [exact (isj_jobs_must_arrive_related Job PR PL sR sL HSA jaR jaL Hja)|].
      apply ar_forall_identity_correspondence. intro tsk.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (isj_is_idle_related Job PR PL sR sL HSA arrR arrL Harr tR tL Ht))|].
      exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (fts_task_served_at_related Task Job jtR jtL Hjt PR PL sR sL HSA HSE arrR arrL Harr tsk tR tL Ht))).
    Qed.

    Definition src_job_of_scheduled_task : Prop :=
      ltac:(body_of (fun s : S.statement_job_of_scheduled_task => s Task Job jtR jaR arrR)).
    Definition tgt_job_of_scheduled_task : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskSchedule_job_of_scheduled_task
        Task dT Job dJ jtL jaL arrL)).
    Theorem job_of_scheduled_task_correspondence : PropSPropRel src_job_of_scheduled_task tgt_job_of_scheduled_task.
    Proof.
      apply ar_imp_correspondence; [exact valid_rel|].
      apply (isj_cover_pstate Job). intros PR PL X.
      apply ar_imp_correspondence; [exact (isj_psr_uniprocessor_related Job PR PL X)|].
      apply (cover_sched PR PL X). intros sR sL Hs.
      have HSA := isj_psr_scheduled_at_related Job PR PL X sR sL Hs.
      have HSE := isj_psr_service_at_related Job PR PL X sR sL Hs.
      apply ar_imp_correspondence; [exact (isj_jobs_come_from_related Job PR PL sR sL HSA arrR arrL Harr)|].
      apply ar_imp_correspondence; [exact (isj_jobs_must_arrive_related Job PR PL sR sL HSA jaR jaL Hja)|].
      apply ar_forall_identity_correspondence. intro tsk.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (isj_psr_scheduled_at_related Job PR PL X sR sL Hs j _ _ Ht))|].
      exact (fts_bool_eq_correspondence _ _ _ _ (fts_task_scheduled_at_related Task Job jtR jtL Hjt PR PL sR sL HSA arrR arrL Harr tsk tR tL Ht) (fts_job_of_task_related Task Job jtR jtL Hjt tsk j)).
    Qed.

    Definition src_job_of_task_scheduled : Prop :=
      ltac:(body_of (fun s : S.statement_job_of_task_scheduled => s Task Job jtR jaR arrR)).
    Definition tgt_job_of_task_scheduled : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskSchedule_job_of_task_scheduled
        Task dT Job dJ jtL jaL arrL)).
    Theorem job_of_task_scheduled_correspondence : PropSPropRel src_job_of_task_scheduled tgt_job_of_task_scheduled.
    Proof.
      apply ar_imp_correspondence; [exact valid_rel|].
      apply (isj_cover_pstate Job). intros PR PL X.
      apply ar_imp_correspondence; [exact (isj_psr_uniprocessor_related Job PR PL X)|].
      apply (cover_sched PR PL X). intros sR sL Hs.
      have HSA := isj_psr_scheduled_at_related Job PR PL X sR sL Hs.
      have HSE := isj_psr_service_at_related Job PR PL X sR sL Hs.
      apply ar_imp_correspondence; [exact (isj_jobs_come_from_related Job PR PL sR sL HSA arrR arrL Harr)|].
      apply ar_imp_correspondence; [exact (isj_jobs_must_arrive_related Job PR PL sR sL HSA jaR jaL Hja)|].
      apply ar_forall_identity_correspondence. intro tsk.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (fts_job_of_task_related Task Job jtR jtL Hjt tsk j))|].
      apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (isj_psr_scheduled_at_related Job PR PL X sR sL Hs j _ _ Ht))|].
      exact (svc_bool_truth_correspondence _ _ (fts_task_scheduled_at_related Task Job jtR jtL Hjt PR PL sR sL HSA arrR arrL Harr tsk tR tL Ht)).
    Qed.

    Definition src_job_of_other_task_scheduled : Prop :=
      ltac:(body_of (fun s : S.statement_job_of_other_task_scheduled => s Task Job jtR jaR arrR)).
    Definition tgt_job_of_other_task_scheduled : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskSchedule_job_of_other_task_scheduled
        Task dT Job dJ jtL jaL arrL)).
    Theorem job_of_other_task_scheduled_correspondence : PropSPropRel src_job_of_other_task_scheduled tgt_job_of_other_task_scheduled.
    Proof.
      apply ar_imp_correspondence; [exact valid_rel|].
      apply (isj_cover_pstate Job). intros PR PL X.
      apply ar_imp_correspondence; [exact (isj_psr_uniprocessor_related Job PR PL X)|].
      apply (cover_sched PR PL X). intros sR sL Hs.
      have HSA := isj_psr_scheduled_at_related Job PR PL X sR sL Hs.
      have HSE := isj_psr_service_at_related Job PR PL X sR sL Hs.
      apply ar_imp_correspondence; [exact (isj_jobs_come_from_related Job PR PL sR sL HSA arrR arrL Harr)|].
      apply ar_imp_correspondence; [exact (isj_jobs_must_arrive_related Job PR PL sR sL HSA jaR jaL Hja)|].
      apply ar_forall_identity_correspondence. intro tsk.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (fts_job_of_task_related Task Job jtR jtL Hjt tsk j)))|].
      apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (isj_psr_scheduled_at_related Job PR PL X sR sL Hs j _ _ Ht))|].
      exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (fts_task_scheduled_at_related Task Job jtR jtL Hjt PR PL sR sL HSA arrR arrL Harr tsk tR tL Ht))).
    Qed.

    Definition src_job_of_other_task_scheduled' : Prop :=
      ltac:(body_of (fun s : S.statement_job_of_other_task_scheduled' => s Task Job jtR jaR arrR)).
    Definition tgt_job_of_other_task_scheduled' : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskSchedule_job_of_other_task_scheduled'
        Task dT Job dJ jtL jaL arrL)).
    Theorem job_of_other_task_scheduled'_correspondence : PropSPropRel src_job_of_other_task_scheduled' tgt_job_of_other_task_scheduled'.
    Proof.
      apply ar_imp_correspondence; [exact valid_rel|].
      apply (isj_cover_pstate Job). intros PR PL X.
      apply ar_imp_correspondence; [exact (isj_psr_uniprocessor_related Job PR PL X)|].
      apply (cover_sched PR PL X). intros sR sL Hs.
      have HSA := isj_psr_scheduled_at_related Job PR PL X sR sL Hs.
      have HSE := isj_psr_service_at_related Job PR PL X sR sL Hs.
      apply ar_imp_correspondence; [exact (isj_jobs_come_from_related Job PR PL sR sL HSA arrR arrL Harr)|].
      apply ar_imp_correspondence; [exact (isj_jobs_must_arrive_related Job PR PL sR sL HSA jaR jaL Hja)|].
      apply ar_forall_identity_correspondence. intro tsk.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (fts_job_of_task_related Task Job jtR jtL Hjt tsk j)))|].
      apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (isj_psr_scheduled_at_related Job PR PL X sR sL Hs j _ _ Ht))|].
      exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (fts_task_served_at_related Task Job jtR jtL Hjt PR PL sR sL HSA HSE arrR arrL Harr tsk tR tL Ht))).
    Qed.

    Definition src_job_of_task_not_served : Prop :=
      ltac:(body_of (fun s : S.statement_job_of_task_not_served => s Task Job jtR jaR arrR)).
    Definition tgt_job_of_task_not_served : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskSchedule_job_of_task_not_served
        Task dT Job dJ jtL jaL arrL)).
    Theorem job_of_task_not_served_correspondence : PropSPropRel src_job_of_task_not_served tgt_job_of_task_not_served.
    Proof.
      apply ar_imp_correspondence; [exact valid_rel|].
      apply (isj_cover_pstate Job). intros PR PL X.
      apply ar_imp_correspondence; [exact (isj_psr_uniprocessor_related Job PR PL X)|].
      apply (cover_sched PR PL X). intros sR sL Hs.
      have HSA := isj_psr_scheduled_at_related Job PR PL X sR sL Hs.
      have HSE := isj_psr_service_at_related Job PR PL X sR sL Hs.
      apply ar_imp_correspondence; [exact (isj_jobs_come_from_related Job PR PL sR sL HSA arrR arrL Harr)|].
      apply ar_imp_correspondence; [exact (isj_jobs_must_arrive_related Job PR PL sR sL HSA jaR jaL Hja)|].
      apply ar_forall_identity_correspondence. intro tsk.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (isj_psr_scheduled_at_related Job PR PL X sR sL Hs j _ _ Ht))|].
      apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (fts_job_of_task_related Task Job jtR jtL Hjt tsk j))|].
      apply ar_imp_correspondence;
        [exact (sub_nat_eq_correspondence _ _ _ _ (isj_psr_service_at_related Job PR PL X sR sL Hs j _ _ Ht)
           (sub_nat_rel_canonical O))|].
      exact (svc_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (fts_task_served_at_related Task Job jtR jtL Hjt PR PL sR sL HSA HSE arrR arrL Harr tsk tR tL Ht))).
    Qed.

    Definition src_task_served_at_eq_job_of_task : Prop :=
      ltac:(body_of (fun s : S.statement_task_served_at_eq_job_of_task => s Task Job jtR jaR arrR)).
    Definition tgt_task_served_at_eq_job_of_task : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_TaskSchedule_task_served_at_eq_job_of_task
        Task dT Job dJ jtL jaL arrL)).
    Theorem task_served_at_eq_job_of_task_correspondence : PropSPropRel src_task_served_at_eq_job_of_task tgt_task_served_at_eq_job_of_task.
    Proof.
      apply ar_imp_correspondence; [exact valid_rel|].
      apply (isj_cover_pstate Job). intros PR PL X.
      apply ar_imp_correspondence; [exact (isj_psr_uniprocessor_related Job PR PL X)|].
      apply (cover_sched PR PL X). intros sR sL Hs.
      have HSA := isj_psr_scheduled_at_related Job PR PL X sR sL Hs.
      have HSE := isj_psr_service_at_related Job PR PL X sR sL Hs.
      apply ar_imp_correspondence; [exact (isj_jobs_come_from_related Job PR PL sR sL HSA arrR arrL Harr)|].
      apply ar_imp_correspondence; [exact (isj_jobs_must_arrive_related Job PR PL sR sL HSA jaR jaL Hja)|].
      apply ar_forall_identity_correspondence. intro tsk.
      apply ar_imp_correspondence; [exact (fts_psr_fully_consuming_related Job PR PL X)|].
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence;
        [exact (svc_bool_truth_correspondence _ _ (fts_psr_has_supply_related Job PR PL X sR sL Hs tR tL Ht))|].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_imp_correspondence; [exact (svc_bool_truth_correspondence _ _ (isj_psr_scheduled_at_related Job PR PL X sR sL Hs j _ _ Ht))|].
      exact (fts_bool_eq_correspondence _ _ _ _ (fts_task_served_at_related Task Job jtR jtL Hjt PR PL sR sL HSA HSE arrR arrL Harr tsk tR tL Ht) (fts_job_of_task_related Task Job jtR jtL Hjt tsk j)).
    Qed.
  End WithArrival.
End Statements.
