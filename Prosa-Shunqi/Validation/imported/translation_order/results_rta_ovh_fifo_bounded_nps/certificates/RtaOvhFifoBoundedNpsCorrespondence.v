From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import RtaOvhFifoBoundedNpsSemanticSource.
From prosa Require Import behavior.all model.processor.overheads model.readiness.basic model.priority.fifo
  model.task.arrival.curves model.job.properties model.composite.valid_task_arrival_sequence
  analysis.definitions.overheads.schedule_change.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRtaOvhFifoBoundedNps ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  OvhArrivalsSeqBaseAdapter OvhArrivalsSeqOperations OvhArrivalsSeqCorrespondence OvhArrivalsCorrespondence
  OvhJitterSvcBaseAdapter OvhJitterSvcNatBoolOperations OvhJitterSvcIntervalOperations
  OvhJitterSvcScheduleOperations OvhJitterSvcJobOperations OvhPreemptionParameterCorrespondence
  OvhPreemptionTimeCorrespondence OvhPriorityDrivenCorrespondence OvhPStateCoverHelpers OvhFactsPreemptionHelpers
  OvhWorkloadCorrespondence OvhPriorityInversionCorrespondence OvhExistenceHelpers OvhHepAtPtHelpers
  OvhTaskPreemptionParametersCorrespondence OvhBusyIntervalPiHelpers OvhStateRel OvhCurvesCorrespondence.
From FoundationCertificates Require OvhRequestBoundFunctionCorrespondence OvhSearchSpaceFifoCorrespondence
  OverheadsCorrespondence OverheadResourceModelCorrespondence.

Module I := ImportedRtaOvhFifoBoundedNps.
Module S := RtaOvhFifoBoundedNpsSemanticSource.RtaOvhFifoBoundedNpsSemanticSource.
Module PP := PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.
Module TPS := TaskPreemptionParametersSemanticSource.TaskPreemptionParametersSemanticSource.
Module SCH := SchedulabilitySemanticSource.SchedulabilitySemanticSource.
Module RBF := OvhRequestBoundFunctionCorrespondence.
Module SSF := OvhSearchSpaceFifoCorrespondence.
Module OVC := OverheadsCorrespondence.
Module ORM := OverheadResourceModelCorrespondence.
Module TPPC := OvhTaskPreemptionParametersCorrespondence.

(** Definition and statement correspondences for [results/rta/ovh/fifo/bounded_nps.v].

    Source side: the extracted definitions and statement specialised at their leading input binders; target
    side: the compiled Lean definitions and the imported Lean theorem type.  Leading inputs: the task and job
    types, the task-cost, arrival-curve, run-to-completion-threshold, job-task, job-cost, job-arrival and
    preemption instances, the task set and the task under analysis, related by the accepted relations (each with
    two-way totals; tasks and jobs by identity).  The overheads processor model is fixed on both sides and
    related by [ovh_psrel] (OvhStateRel.v); the generic chain helpers are replayed at its universe instance (Ovh*.v,
    see their headers).  Arrival sequences and schedules are covered in both directions, the overhead bounds and
    the busy-window, response-time and offset values are related by [SubNatRel].  The source's section-local
    [overhead_bound] is unfolded in both definitions; [total_request_bound_function] and the FIFO
    [is_in_search_space] are the accepted definition certificates (re-bound to the replayed arrivals modules);
    [valid_task_arrival_sequence] unfolds into the accepted arrival-sequence, job-cost, task-set and
    arrival-curve relations; the FIFO policy is related through job arrivals; the basic readiness model is fixed
    on both sides and related pointwise through [pending]; schedules related by [ovh_psrel] are also related by the
    accepted constructor-wise overheads relation, which gives the accepted overhead-resource-model certificate.
    No source or target theorem is used. *)

Local Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Local Ltac type_of_term t := let T := type of t in exact T.

Section Rta.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
  Let PR := prosa.model.processor.overheads.processor_state Job.
  Let PL := I.Prosa_Model_Processor_Overheads_processor_state Job dJ.
  Let X := ovh_psrel Job.
  Variable tcR : prosa.model.task.concept.TaskCost Task.
  Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
  Hypothesis Htc : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).
  Variable maR : prosa.model.task.arrival.curves.MaxArrivals Task.
  Variable maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT.
  Hypothesis Hma : CvMaxArrivalsRel Task maR maL.
  Variable rR : TPS.TaskRunToCompletionThreshold Task.
  Variable rL : I.Prosa_Model_Task_Preemption_Parameters_TaskRunToCompletionThreshold Task dT.
  Hypothesis Hr : TPPC.TppRtctRel Task rR rL.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable jpR : PP.JobPreemptable Job.
  Variable jpL : I.Prosa_Model_Preemption_Parameter_JobPreemptable Job dJ.
  Hypothesis Hjp : PpJobPreemptableRel Job jpR jpL.

  Local Ltac imp H := apply ar_imp_correspondence; [exact H|].

  (** *** Task-level relations *)

  Lemma rof_task_cost_of_job_related (j : Job) :
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR (@prosa.model.task.concept.job_task Job Task jtR j))
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j)).
  Proof.
    exact (isj_lean_transport
      (fun v => SubNatRel (@prosa.model.task.concept.task_cost Task tcR (@prosa.model.task.concept.job_task Job Task jtR j))
        (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL v)) _ _ (Hjt j) (Htc _)).
  Qed.

  Section Arr.
    Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
    Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
    Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

    Lemma rof_valid_job_costs_rel :
      PropSPropRel (@prosa.model.task.concept.arrivals_have_valid_job_costs Task tcR Job jtR costR arrR)
        (I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task dT tcL Job dJ jtL costL arrL).
    Proof.
      unfold prosa.model.task.concept.arrivals_have_valid_job_costs, prosa.model.task.concept.valid_job_cost.
      cbn [I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs I.Prosa_Model_Task_Concept_valid_job_cost].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
      exact (ar_bool_truth_correspondence _ _
        (svc_decide_le_related _ _ _ _ (Hcost j) (rof_task_cost_of_job_related j))).
    Qed.

    Lemma rof_all_jobs_from_taskset_rel tsR tsL (Hts : ArListRel tsR tsL) :
      PropSPropRel (@prosa.model.task.concept.all_jobs_from_taskset Task Job jtR arrR tsR)
        (I.Prosa_Model_Task_Concept_all_jobs_from_taskset Task dT Job dJ jtL arrL tsL).
    Proof.
      unfold prosa.model.task.concept.all_jobs_from_taskset.
      cbn [I.Prosa_Model_Task_Concept_all_jobs_from_taskset].
      apply ar_forall_identity_correspondence => j.
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
      rewrite -(imported_eq_to_coq_eq _ _ (Hjt j)).
      exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task _ _ _ Hts)).
    Qed.

    Lemma rof_valid_task_arrival_sequence_rel tsR tsL (Hts : ArListRel tsR tsL) :
      PropSPropRel
        (@prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence
          Task tcR maR Job jtR costR jaR tsR arrR)
        (I.Prosa_Model_Composite_ValidTaskArrivalSequence_valid_task_arrival_sequence
          Task dT tcL maL Job dJ jtL costL jaL tsL arrL).
    Proof.
      unfold prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence.
      cbn [I.Prosa_Model_Composite_ValidTaskArrivalSequence_valid_task_arrival_sequence].
      apply ar_and_correspondence;
        [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
      apply ar_and_correspondence; [exact rof_valid_job_costs_rel|].
      apply ar_and_correspondence; [exact (rof_all_jobs_from_taskset_rel tsR tsL Hts)|].
      apply ar_and_correspondence.
      - exact (taskset_respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsR tsL Hts
          maR maL Hma).
      - exact (valid_taskset_arrival_curve_correspondence Task tsR tsL _ _ Hts Hma).
    Qed.

    Lemma rof_positive_costs_rel :
      PropSPropRel (@prosa.model.job.properties.arrivals_have_positive_job_costs Job costR arrR)
        (I.Prosa_Model_Job_Properties_arrivals_have_positive_job_costs Job dJ costL arrL).
    Proof.
      unfold prosa.model.job.properties.arrivals_have_positive_job_costs.
      cbn [I.Prosa_Model_Job_Properties_arrivals_have_positive_job_costs].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
      exact (ar_bool_truth_correspondence _ _ (ex_job_cost_positive_related Job costR costL Hcost j)).
    Qed.
  End Arr.

  (** *** Schedule-level relations *)

  Lemma rof_ovh_sched sR sL (Hs : IsjPSchedRel Job PR PL X sR sL) : OVC.OvhScheduleRel Job sR sL.
  Proof.
    intros tR tL Ht.
    refine (sub_imported_eq_trans _ _ _ _ (Hs tR tL Ht)). cbn.
    destruct (sR tR) as [| a b | a | j | j]; cbn; try destruct a; try destruct b; exact (@Lean.eq_refl _ _).
  Qed.

  Section Pair.
    Variable sR : @prosa.behavior.schedule.schedule Job PR.
    Variable sL : I.Prosa_Behavior_Schedule_schedule_inst4 Job dJ PL.
    Hypothesis Hs : IsjPSchedRel Job PR PL X sR sL.

    Let Hsa := isj_psr_scheduled_at_related Job PR PL X sR sL Hs.
    Let COMPLETED := fpre_completed_by_related Job costR costL Hcost PR PL X sR sL Hs.

    Lemma rof_basic_ready_rel :
      FpreJrAt Job jaR jaL costR costL PR PL sR sL
        (@prosa.model.readiness.basic.basic_ready_instance Job PR jaR costR)
        (I.Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job dJ PL jaL costL).
    Proof.
      intros j tR tL Ht.
      exact (fpre_pending_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs j tR tL Ht).
    Qed.

    Lemma rof_preempted_at_related (j : Job) tR tL (Ht : SubNatRel tR tL) :
      ArBoolRel (@PP.preempted_at Job costR PR sR j tR)
        (I.Prosa_Model_Preemption_Parameter_preempted_at_inst4 Job dJ costL PL sL j tL).
    Proof.
      unfold PP.preempted_at.
      cbn [I.Prosa_Model_Preemption_Parameter_preempted_at_inst4].
      rewrite -subn1.
      apply ar_bool_and_related; [apply ar_bool_and_related|].
      - exact (Hsa j _ _ (svc_target_sub_related _ _ _ _ Ht (sub_nat_rel_canonical 1))).
      - exact (svc_bool_not_related _ _ (COMPLETED j tR tL Ht)).
      - exact (svc_bool_not_related _ _ (Hsa j tR tL Ht)).
    Qed.

    Lemma rof_no_superfluous_rel pR pL (Hp : FpreJLFPRel Job pR pL) :
      PropSPropRel
        (@PP.no_superfluous_preemptions Job costR (@prosa.model.priority.coercion.JLFP_to_JLDP Job pR) PR sR)
        (I.Prosa_Model_Preemption_Parameter_no_superfluous_preemptions_inst4 Job dJ costL
          (I.Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job dJ pL) PL sL).
    Proof.
      unfold PP.no_superfluous_preemptions.
      cbn [I.Prosa_Model_Preemption_Parameter_no_superfluous_preemptions_inst4].
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_identity_correspondence. intro jhp.
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _ (rof_preempted_at_related j tR tL Ht))|].
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hsa jhp tR tL Ht))|].
      exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (Hp j jhp))).
    Qed.
  End Pair.

  Lemma rof_fifo_rel :
    FpreJLFPRel Job (@prosa.model.priority.fifo.FIFO Job jaR) (I.Prosa_Model_Priority_Fifo_FIFO Job dJ jaL).
  Proof. intros x y. exact (ar_decide_le_related _ _ _ _ (Hja x) (Hja y)). Qed.

  Lemma rof_job_of_task_related (tsk : Task) (j : Job) :
    ArBoolRel (@prosa.model.task.concept.job_of_task Job Task jtR tsk j)
      (I.Prosa_Model_Task_Concept_job_of_task Job dJ Task dT jtL tsk j).
  Proof.
    unfold prosa.model.task.concept.job_of_task.
    cbn [I.Prosa_Model_Task_Concept_job_of_task].
    refine (isj_lean_transport
      (fun v => ArBoolRel (@prosa.model.task.concept.job_task Job Task jtR j == tsk)
        (I.Decidable_decide (Lean.eq v tsk) (dT v tsk))) _ _ (Hjt j) _).
    exact (ari_decide_eq_related Task _ tsk).
  Qed.

  (** *** The two definitions *)

  Section Defs.
    Variable tsR : seq Task.
    Variable tsL : I.List Task.
    Hypothesis Hts : ArListRel tsR tsL.
    Variables (DR CR PRb : nat) (DL CL PLb : Lean.Nat).
    Hypotheses (HD : SubNatRel DR DL) (HC : SubNatRel CR CL) (HP : SubNatRel PRb PLb).

    Let ONE := sub_nat_rel_canonical (S O).
    Let TRBF dR dL (Hd : SubNatRel dR dL) :=
      RBF.total_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts dR dL Hd.
    Let OB dR dL (Hd : SubNatRel dR dL) :=
      sub_mul_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ HD HC) HP)
        (sub_add_correspondence _ _ _ _ ONE (ari_sum_related Task _ _ _ _ (fun tsk => Hma tsk _ _ Hd) Hts)).

    Theorem busy_window_recurrence_solution_correspondence (LR : nat) (LL : Lean.Nat) (HL : SubNatRel LR LL) :
      PropSPropRel (@S.busy_window_recurrence_solution Task tcR maR tsR DR CR PRb LR)
        (I.Prosa_Results_Rta_Ovh_Fifo_BoundedNps_busy_window_recurrence_solution Task dT tcL maL tsL DL CL PLb LL).
    Proof.
      unfold S.busy_window_recurrence_solution. cbv zeta.
      cbn [I.Prosa_Results_Rta_Ovh_Fifo_BoundedNps_busy_window_recurrence_solution].
      apply ar_and_correspondence.
      - exact (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) HL).
      - exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (OB _ _ HL) (TRBF _ _ HL)) HL).
    Qed.

    Theorem rta_recurrence_solution_correspondence (LR : nat) (LL : Lean.Nat) (HL : SubNatRel LR LL)
        (RR : nat) (RL : Lean.Nat) (HR : SubNatRel RR RL) :
      PropSPropRel (@S.rta_recurrence_solution Task tcR maR tsR DR CR PRb LR RR)
        (I.Prosa_Results_Rta_Ovh_Fifo_BoundedNps_rta_recurrence_solution Task dT tcL maL tsL DL CL PLb LL RL).
    Proof.
      unfold S.rta_recurrence_solution. cbv zeta.
      cbn [I.Prosa_Results_Rta_Ovh_Fifo_BoundedNps_rta_recurrence_solution].
      apply ar_forall_nat_correspondence. intros AR AL HA.
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _
          (SSF.is_in_search_space_correspondence Task tcR tcL Htc tsR tsL Hts maR maL Hma LR AR LL AL HL HA))|].
      apply ar_exists_nat_correspondence. intros FR' FL' HF.
      apply ar_and_correspondence.
      - exact (sub_nat_le_correspondence _ _ _ _
          (sub_add_correspondence _ _ _ _ (OB _ _ HF) (TRBF _ _ (svc_target_add_related _ _ _ _ HA ONE))) HF).
      - exact (sub_nat_le_correspondence _ _ _ _ HF (svc_target_add_related _ _ _ _ HA HR)).
    Qed.
  End Defs.

  (** *** The theorem *)

  Definition src_uniprocessor_response_time_bound_fifo : Prop :=
    ltac:(body_of (fun s : S.statement_uniprocessor_response_time_bound_fifo =>
      s Task tcR maR rR Job jtR costR jaR jpR)).
  Definition tgt_uniprocessor_response_time_bound_fifo : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Results_Rta_Ovh_Fifo_BoundedNps_uniprocessor_response_time_bound_fifo
        Task dT tcL maL rL Job dJ jtL costL jaL jpL)).

  Theorem uniprocessor_response_time_bound_fifo_correspondence :
    PropSPropRel src_uniprocessor_response_time_bound_fifo tgt_uniprocessor_response_time_bound_fifo.
  Proof.
    unfold src_uniprocessor_response_time_bound_fifo, tgt_uniprocessor_response_time_bound_fifo.
    apply (isj_forall_cover_sprop _ _ ArListRel ar_list_to_imported ar_list_to_rocq
      (fun xs => @Lean.eq_refl _ _) (fun xs => ar_list_target_roundtrip xs)).
    intros tsR tsL Hts.
    apply ar_forall_identity_correspondence. intro tsk.
    imp (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).
    apply (fpre_forall_arr Job). intros arrR arrL Harr.
    imp (rof_valid_task_arrival_sequence_rel arrR arrL Harr tsR tsL Hts).
    imp (TPPC.valid_task_run_to_completion_threshold_correspondence Task Job tcR tcL Htc rR rL Hr
      jtR jtL Hjt costR costL Hcost jpR jpL Hjp arrR arrL Harr tsk).
    imp (rof_positive_costs_rel arrR arrL Harr).
    apply (fpre_forall_sched Job PR PL X). intros sR sL Hs.
    imp (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr _ _
      (rof_basic_ready_rel sR sL Hs)).
    imp (ex_work_conserving_related Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr _ _
      (rof_basic_ready_rel sR sL Hs)).
    imp (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL Harr jpR jpL Hjp).
    imp (fpre_respects_jlfp_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr _ _
      (rof_basic_ready_rel sR sL Hs) jpR jpL Hjp _ _ rof_fifo_rel).
    imp (rof_no_superfluous_rel sR sL Hs _ _ rof_fifo_rel).
    apply ar_forall_nat_correspondence. intros DR DL HD.
    apply ar_forall_nat_correspondence. intros CR CL HC.
    apply ar_forall_nat_correspondence. intros PRb PLb HP.
    imp (ORM.overhead_resource_model_correspondence Job sR sL (rof_ovh_sched sR sL Hs) _ _ _ _ _ _ HD HC HP).
    apply ar_forall_nat_correspondence. intros LR LL HL.
    imp (busy_window_recurrence_solution_correspondence tsR tsL Hts DR CR PRb DL CL PLb HD HC HP LR LL HL).
    apply ar_forall_nat_correspondence. intros RR RL HR.
    imp (rta_recurrence_solution_correspondence tsR tsL Hts DR CR PRb DL CL PLb HD HC HP LR LL HL RR RL HR).
    unfold SCH.task_response_time_bound.
    cbn [I.Prosa_Analysis_Definitions_Schedulability_task_response_time_bound_inst8].
    apply ar_forall_identity_correspondence. intro j.
    imp (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    imp (ar_bool_truth_correspondence _ _ (rof_job_of_task_related tsk j)).
    unfold prosa.behavior.service.job_response_time_bound.
    cbn [I.Prosa_Behavior_Service_job_response_time_bound_inst4].
    exact (ar_bool_truth_correspondence _ _
      (fpre_completed_by_related Job costR costL Hcost PR PL X sR sL Hs j _ _
        (svc_target_add_related _ _ _ _ (Hja j) HR))).
  Qed.
End Rta.
