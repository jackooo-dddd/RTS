From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import FactsJitterSemanticSource.
From prosa Require Import behavior.all model.processor.platform_properties model.schedule.scheduled
  model.priority.classes model.schedule.work_conserving model.readiness.basic model.readiness.jitter
  model.task.jitter analysis.definitions.delay_propagation.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsJitter ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers
  ArrivalsCorrespondence CurvesCorrespondence DelayPropagationCorrespondence.

Module I := ImportedFactsJitter.
Module S := FactsJitterSemanticSource.FactsJitterSemanticSource.
Module PP := PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.
Module PDS := PriorityDrivenSemanticSource.PriorityDrivenSemanticSource.
Module SCH := SchedulabilitySemanticSource.SchedulabilitySemanticSource.
Module DP := prosa.analysis.definitions.delay_propagation.

(** Statement correspondences for [analysis/facts/jitter.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs (task and job types, the job-task, original arrival,
    task-jitter and job-jitter classes, the arrival curve); target side: the
    imported Lean theorem types.  Inputs: [job_task] by [Lean.eq],
    [job_arrival] by [ArJobArrivalRel], [task_jitter], [job_jitter] and the
    arrival curve pointwise on related Nats.  Inputs quantified inside a
    statement are covered in both directions: arrival sequences
    ([fpre_forall_arr]), task sets (lists), processor models (the accepted
    [isj_cover_pstate]), schedules through the processor-model relation
    ([fpre_forall_sched]), job costs and task costs (pointwise), FP policies
    (pointwise on Booleans), [JobPreemptable] instances ([fpre_forall_jp]),
    tasks, jobs, instants and durations.

    The source-local instances are related directly: [release_as_arrival]
    pointwise (arrival plus jitter), [release_curve] by the accepted
    propagated-arrival-curve argument, and the readiness instances
    [jitter_ready_instance] and [basic_ready_instance] (the latter over the
    release times) pointwise at the statement's schedule pair.  The release
    sequence is the accepted propagated-arrival-sequence certificate; arrival
    curves, arrival sequences, completion, pendency, preemption times and
    scheduled jobs are the accepted curves, arrival, preemption-facts and
    processor-model certificates; work conservation, schedule validity,
    FP-policy compliance and response-time bounds are related by unfolding.
    No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma jit_exists_identity (T : Type) (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (exists x, PR x) (I.Exists T PL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (I.Exists_intro T PL x (prop_to_sprop _ _ (H x) Hx)).
  - intros [x Hx]. apply strictly_inhabits. exists x. exact (sprop_to_prop _ _ (H x) Hx).
Qed.

(** Options of jobs, through the canonical conversion. *)
Definition jit_opt_to_imported {T : Type} (o : option T) : I.Option T :=
  match o with Some x => I.Option_some T x | None => I.Option_none T end.

Lemma jit_ohead_related {T : Type} (l : seq T) (lL : I.List T) :
  ArListRel l lL -> Lean.eq (jit_opt_to_imported (ohead l)) (I.List_head__q T lL).
Proof.
  intro H.
  refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_congr (I.List_head__q T) _ _ H)).
  destruct l; exact (@Lean.eq_refl _ _).
Qed.

Lemma jit_opt_eq_correspondence {T : Type} (o1 o2 : option T) (oL1 oL2 : I.Option T) :
  Lean.eq (jit_opt_to_imported o1) oL1 -> Lean.eq (jit_opt_to_imported o2) oL2 ->
  PropSPropRel (Logic.eq o1 o2) (Lean.eq oL1 oL2).
Proof.
  intros H1 H2. apply prop_sprop_rel_intro.
  - intro Heq. destruct Heq.
    exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ H1) H2).
  - intro Heq. apply strictly_inhabits.
    have Hc : Lean.eq (jit_opt_to_imported o1) (jit_opt_to_imported o2) :=
      sub_imported_eq_trans _ _ _ H1 (sub_imported_eq_trans _ _ _ Heq (sub_imported_eq_sym _ _ H2)).
    have E := imported_eq_to_coq_eq _ _ Hc.
    destruct o1, o2; cbn in E; try discriminate; [injection E as ->|]; reflexivity.
Qed.

Section Jitter.
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
  Variable tjR : prosa.model.task.jitter.TaskJitter Task.
  Variable tjL : I.Prosa_Model_Task_Jitter_TaskJitter Task dT.
  Hypothesis Htj : forall tsk : Task,
    SubNatRel (@prosa.model.task.jitter.task_jitter Task tjR tsk)
      (I.Prosa_Model_Task_Jitter_TaskJitter_task_jitter Task dT tjL tsk).
  Variable jjR : prosa.model.readiness.jitter.JobJitter Job.
  Variable jjL : I.Prosa_Model_Readiness_Jitter_JobJitter Job dJ.
  Hypothesis Hjj : forall j : Job,
    SubNatRel (@prosa.model.readiness.jitter.job_jitter Job jjR j)
      (I.Prosa_Model_Readiness_Jitter_JobJitter_job_jitter Job dJ jjL j).

  (** *** The release-time reinterpretation *)

  Let relR := @DP.release_as_arrival Job jaR jjR.
  Let relL := I.Prosa_Analysis_Facts_Jitter_release_as_arrival Job dJ jaL jjL.

  Lemma jit_release_rel : ArJobArrivalRel Job relR relL.
  Proof.
    intro j.
    change (SubNatRel (@prosa.behavior.job.job_arrival Job jaR j + @prosa.model.readiness.jitter.job_jitter Job jjR j)
      (svc_target_add (I.Prosa_Behavior_Job_JobArrival_job_arrival Job dJ jaL j)
        (I.Prosa_Model_Readiness_Jitter_JobJitter_job_jitter Job dJ jjL j))).
    exact (svc_target_add_related _ _ _ _ (Hja j) (Hjj j)).
  Qed.

  Lemma jit_release_sequence_rel arrR arrL (Harr : ArArrivalSequenceRel Job arrR arrL) :
    ArArrivalSequenceRel Job (@DP.release_sequence Job jaR jjR arrR)
      (I.Prosa_Analysis_Definitions_DelayPropagation_release_sequence Job dJ jaL jjL arrL).
  Proof.
    intros tR tL Ht.
    exact (propagated_arrival_sequence_correspondence Job Job jaR jaL Hja (fun j => j) arrR arrL Harr
      (fun j => [:: j]) (fun j => I.List_cons Job j (I.List_nil Job)) (fun j => @Lean.eq_refl _ _)
      jjR (I.Prosa_Model_Readiness_Jitter_JobJitter_job_jitter Job dJ jjL) Hjj tR tL Ht).
  Qed.

  Lemma jit_release_curve_rel maR maL (Hma : CvMaxArrivalsRel Task maR maL) :
    CvMaxArrivalsRel Task (@DP.release_curve Task maR tjR)
      (I.Prosa_Analysis_Facts_Jitter_release_curve Task dT maL tjL).
  Proof.
    intros tsk nR nL Hn.
    refine (ari_lean_transport (fun x => SubNatRel _ (I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task dT
      (I.Prosa_Analysis_Facts_Jitter_release_curve Task dT maL tjL) tsk x)) _ _ Hn _).
    destruct nR as [|n].
    - exact (@Lean.eq_refl _ _).
    - exact (Hma tsk _ _ (sub_add_correspondence _ _ _ _ (sub_nat_rel_canonical n.+1) (Htj tsk))).
  Qed.

  (** *** Task-set and cost properties *)

  Lemma jit_job_task_eq_rel (j : Job) (tsk : Task) :
    PropSPropRel (@prosa.model.task.concept.job_task Job Task jtR j = tsk)
      (Lean.eq (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j) tsk).
  Proof.
    have E := imported_eq_to_coq_eq _ _ (Hjt j). rewrite -E.
    exact (isj_eq_identity_correspondence Task _ tsk).
  Qed.

  Lemma jit_valid_jitter_bounds_rel tsR tsL (Hts : ArListRel tsR tsL) :
    PropSPropRel (@prosa.model.task.jitter.valid_jitter_bounds Task tjR Job jtR jjR tsR)
      (I.Prosa_Model_Task_Jitter_valid_jitter_bounds Task dT tjL Job dJ jtL jjL tsL).
  Proof.
    unfold prosa.model.task.jitter.valid_jitter_bounds, prosa.model.task.jitter.valid_jitter.
    cbn [I.Prosa_Model_Task_Jitter_valid_jitter_bounds I.Prosa_Model_Task_Jitter_valid_jitter].
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts))|].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (jit_job_task_eq_rel j tsk)|].
    exact (sub_nat_le_correspondence _ _ _ _ (Hjj j) (Htj tsk)).
  Qed.

  Lemma jit_task_mem_related (j : Job) tsR tsL (Hts : ArListRel tsR tsL) :
    ArBoolRel (@prosa.model.task.concept.job_task Job Task jtR j \in tsR)
      (ar_target_decide_mem Task (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j) tsL).
  Proof.
    exact (isj_lean_transport (fun v => ArBoolRel (@prosa.model.task.concept.job_task Job Task jtR j \in tsR)
      (ar_target_decide_mem Task v tsL)) _ _ (Hjt j) (ar_decide_mem_related Task _ _ _ Hts)).
  Qed.

  Lemma jit_all_jobs_from_taskset_rel arrR arrL (Harr : ArArrivalSequenceRel Job arrR arrL) tsR tsL
      (Hts : ArListRel tsR tsL) :
    PropSPropRel (@prosa.model.task.concept.all_jobs_from_taskset Task Job jtR arrR tsR)
      (I.Prosa_Model_Task_Concept_all_jobs_from_taskset Task dT Job dJ jtL arrL tsL).
  Proof.
    unfold prosa.model.task.concept.all_jobs_from_taskset.
    cbn [I.Prosa_Model_Task_Concept_all_jobs_from_taskset].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    exact (ar_bool_truth_correspondence _ _ (jit_task_mem_related j tsR tsL Hts)).
  Qed.

  Lemma jit_job_of_task_related (tsk : Task) (j : Job) :
    ArBoolRel (@prosa.model.task.concept.job_of_task Job Task jtR tsk j)
      (I.Prosa_Model_Task_Concept_job_of_task Job dJ Task dT jtL tsk j).
  Proof.
    unfold prosa.model.task.concept.job_of_task.
    cbn [I.Prosa_Model_Task_Concept_job_of_task].
    exact (isj_lean_transport
      (fun v => ArBoolRel (@prosa.model.task.concept.job_task Job Task jtR j == tsk)
        (I.Decidable_decide (Lean.eq v tsk) (dT v tsk))) _ _ (Hjt j) (ari_decide_eq_related Task _ tsk)).
  Qed.

  Definition JitTaskCostRel (tcR : prosa.model.task.concept.TaskCost Task)
      (tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT) : SProp :=
    forall tsk : Task, SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).

  Lemma jit_forall_task_cost (PR : prosa.model.task.concept.TaskCost Task -> Prop)
      (PL : I.Prosa_Model_Task_Concept_TaskCost Task dT -> SProp) :
    (forall tcR tcL, JitTaskCostRel tcR tcL -> PropSPropRel (PR tcR) (PL tcL)) ->
    PropSPropRel (forall tc, PR tc) (forall tc, PL tc).
  Proof.
    apply (isj_forall_cover_sprop _ _ JitTaskCostRel
      (fun tcR => I.Prosa_Model_Task_Concept_TaskCost_mk Task dT
        (fun tsk => sub_nat_to_imported (@prosa.model.task.concept.task_cost Task tcR tsk)))
      (fun tcL => ((fun tsk => sub_nat_to_rocq (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk))
        : prosa.model.task.concept.TaskCost Task))).
    - intros tcR tsk. exact (sub_nat_rel_canonical _).
    - intros tcL tsk. exact (sub_nat_rel_surjective _).
  Qed.

  Lemma jit_forall_job_cost (PR : prosa.behavior.job.JobCost Job -> Prop)
      (PL : I.Prosa_Behavior_Job_JobCost Job dJ -> SProp) :
    (forall cR cL, SvcJobCostRel Job cR cL -> PropSPropRel (PR cR) (PL cL)) ->
    PropSPropRel (forall c, PR c) (forall c, PL c).
  Proof.
    exact (isj_forall_cover_sprop _ _ (SvcJobCostRel Job) (svc_import_job_cost Job) (svc_export_job_cost Job)
      (svc_job_cost_import Job) (svc_job_cost_export Job) PR PL).
  Qed.

  Lemma jit_valid_job_costs_rel tcR tcL (Htc : JitTaskCostRel tcR tcL) costR costL
      (Hcost : SvcJobCostRel Job costR costL) arrR arrL (Harr : ArArrivalSequenceRel Job arrR arrL) :
    PropSPropRel (@prosa.model.task.concept.arrivals_have_valid_job_costs Task tcR Job jtR costR arrR)
      (I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task dT tcL Job dJ jtL costL arrL).
  Proof.
    unfold prosa.model.task.concept.arrivals_have_valid_job_costs, prosa.model.task.concept.valid_job_cost.
    cbn [I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs I.Prosa_Model_Task_Concept_valid_job_cost].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    apply ar_bool_truth_correspondence.
    apply svc_decide_le_related; [exact (Hcost j)|].
    exact (isj_lean_transport (fun v => SubNatRel (@prosa.model.task.concept.task_cost Task tcR
        (@prosa.model.task.concept.job_task Job Task jtR j))
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL v)) _ _ (Hjt j) (Htc _)).
  Qed.

  Definition JitFPRel (fpR : prosa.model.priority.definitions.FP_policy Task)
      (fpL : I.Prosa_Model_Priority_Definitions_FP_policy Task dT) : SProp :=
    forall x y : Task, ArBoolRel (@prosa.model.priority.definitions.hep_task Task fpR x y)
      (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fpL x y).

  Lemma jit_forall_fp (PR : prosa.model.priority.definitions.FP_policy Task -> Prop)
      (PL : I.Prosa_Model_Priority_Definitions_FP_policy Task dT -> SProp) :
    (forall fpR fpL, JitFPRel fpR fpL -> PropSPropRel (PR fpR) (PL fpL)) ->
    PropSPropRel (forall p, PR p) (forall p, PL p).
  Proof.
    apply (isj_forall_cover_sprop _ _ JitFPRel
      (fun fpR => I.Prosa_Model_Priority_Definitions_FP_policy_mk Task dT
        (fun x y => ar_bool_to_imported (@prosa.model.priority.definitions.hep_task Task fpR x y)))
      (fun fpL => ((fun x y => ar_bool_to_rocq (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fpL x y))
        : prosa.model.priority.definitions.FP_policy Task))).
    - intros fpR x y. exact (@Lean.eq_refl _ _).
    - intros fpL x y. exact (ar_bool_target_roundtrip _).
  Qed.

  Lemma jit_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
    (forall xsR xsL, ArListRel xsR xsL -> PropSPropRel (PR xsR) (PL xsL)) ->
    PropSPropRel (forall xs, PR xs) (forall xs, PL xs).
  Proof.
    apply (isj_forall_cover_sprop _ _ ArListRel ar_list_to_imported ar_list_to_rocq).
    - intro xs. exact (@Lean.eq_refl _ _).
    - intro xs. exact (ar_list_target_roundtrip xs).
  Qed.

  (** *** A fixed processor-model and schedule pair *)

  Section Pair.
    Variable PR : prosa.behavior.schedule.ProcessorState Job.
    Variable PL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
    Variable X : IsjPSRel Job PR PL.
    Variable sR : @prosa.behavior.schedule.schedule Job PR.
    Variable sL : I.Prosa_Behavior_Schedule_schedule Job dJ PL.
    Hypothesis Hs : IsjPSchedRel Job PR PL X sR sL.
    Variable costR : prosa.behavior.job.JobCost Job.
    Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
    Hypothesis Hcost : SvcJobCostRel Job costR costL.

    Let Hsa := isj_psr_scheduled_at_related Job PR PL X sR sL Hs.

    (** Readiness pointwise at this schedule pair, for any arrival instances. *)
    Definition JitReadyAt ja'R ja'L (jrR : @prosa.behavior.ready.JobReady Job PR costR ja'R)
        (jrL : I.Prosa_Behavior_Ready_JobReady Job dJ PL costL ja'L) : SProp :=
      forall j tR tL, SubNatRel tR tL ->
        ArBoolRel (@prosa.behavior.ready.job_ready Job PR costR ja'R jrR sR j tR)
          (I.Prosa_Behavior_Ready_JobReady_job_ready Job dJ PL costL ja'L jrL sL j tL).

    Lemma jit_jitter_ready_rel :
      JitReadyAt jaR jaL (@prosa.model.readiness.jitter.jitter_ready_instance Job PR jaR costR jjR)
        (I.Prosa_Model_Readiness_Jitter_jitter_ready_instance Job dJ jaL jjL PL costL).
    Proof.
      intros j tR tL Ht.
      change (ArBoolRel (prosa.model.readiness.jitter.is_released j tR
          && ~~ @prosa.behavior.service.completed_by Job PR sR costR j tR)
        (I.Bool_and (I.Prosa_Model_Readiness_Jitter_is_released Job dJ jaL jjL j tL)
          (I.Bool_not (I.Prosa_Behavior_Service_completed_by Job dJ PL sL costL j tL)))).
      apply ar_bool_and_related.
      - unfold prosa.model.readiness.jitter.is_released.
        cbn [I.Prosa_Model_Readiness_Jitter_is_released].
        exact (svc_decide_le_related _ _ _ _ (svc_target_add_related _ _ _ _ (Hja j) (Hjj j)) Ht).
      - exact (svc_bool_not_related _ _ (fpre_completed_by_related Job costR costL Hcost PR PL X sR sL Hs j tR tL Ht)).
    Qed.

    Lemma jit_basic_ready_rel :
      JitReadyAt relR relL (@prosa.model.readiness.basic.basic_ready_instance Job PR relR costR)
        (I.Prosa_Model_Readiness_Basic_basic_ready_instance Job dJ PL relL costL).
    Proof.
      intros j tR tL Ht.
      exact (fpre_pending_related Job relR relL jit_release_rel costR costL Hcost PR PL X sR sL Hs j tR tL Ht).
    Qed.

    Section Ready.
      Variable ja'R : prosa.behavior.job.JobArrival Job.
      Variable ja'L : I.Prosa_Behavior_Job_JobArrival Job dJ.
      Variable jrR : @prosa.behavior.ready.JobReady Job PR costR ja'R.
      Variable jrL : I.Prosa_Behavior_Ready_JobReady Job dJ PL costL ja'L.
      Hypothesis Hjr : JitReadyAt ja'R ja'L jrR jrL.

      Lemma jit_must_be_ready_rel :
        PropSPropRel (@prosa.behavior.ready.jobs_must_be_ready_to_execute Job ja'R PR sR costR jrR)
          (I.Prosa_Behavior_Ready_jobs_must_be_ready_to_execute Job dJ ja'L PL sL costL jrL).
      Proof.
        unfold prosa.behavior.ready.jobs_must_be_ready_to_execute.
        cbn [I.Prosa_Behavior_Ready_jobs_must_be_ready_to_execute].
        apply ar_forall_identity_correspondence. intro j.
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hsa j _ _ Ht))|].
        exact (ar_bool_truth_correspondence _ _ (Hjr j tR tL Ht)).
      Qed.

      Lemma jit_backlogged_related (j : Job) tR tL (Ht : SubNatRel tR tL) :
        ArBoolRel (@prosa.behavior.ready.backlogged Job PR costR ja'R jrR sR j tR)
          (I.Prosa_Behavior_Ready_backlogged Job dJ PL costL ja'L jrL sL j tL).
      Proof.
        unfold prosa.behavior.ready.backlogged. cbn [I.Prosa_Behavior_Ready_backlogged].
        exact (ar_bool_and_related _ _ _ _ (Hjr j tR tL Ht) (svc_bool_not_related _ _ (Hsa j tR tL Ht))).
      Qed.

      Section Arr.
        Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
        Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
        Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

        Lemma jit_valid_schedule_rel :
          PropSPropRel (@prosa.behavior.ready.valid_schedule Job ja'R PR sR costR jrR arrR)
            (I.Prosa_Behavior_Ready_valid_schedule Job dJ ja'L PL sL costL jrL arrL).
        Proof.
          unfold prosa.behavior.ready.valid_schedule.
          cbn [I.Prosa_Behavior_Ready_valid_schedule].
          apply ar_and_correspondence; [exact (fpre_come_from_rel Job PR PL X sR sL Hs arrR arrL Harr)|].
          exact jit_must_be_ready_rel.
        Qed.

        Lemma jit_work_conserving_rel :
          PropSPropRel (@prosa.model.schedule.work_conserving.work_conserving Job ja'R costR PR jrR arrR sR)
            (I.Prosa_Model_Schedule_WorkConserving_work_conserving Job dJ ja'L costL PL jrL arrL sL).
        Proof.
          unfold prosa.model.schedule.work_conserving.work_conserving.
          cbn [I.Prosa_Model_Schedule_WorkConserving_work_conserving].
          apply ar_forall_identity_correspondence. intro j.
          apply ar_forall_nat_correspondence. intros tR tL Ht.
          apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
          apply ar_imp_correspondence;
            [exact (ar_bool_truth_correspondence _ _ (jit_backlogged_related j tR tL Ht))|].
          apply jit_exists_identity. intro jo.
          exact (ar_bool_truth_correspondence _ _ (Hsa jo tR tL Ht)).
        Qed.

        Lemma jit_respects_fp_rel jpR jpL (Hjp : PpJobPreemptableRel Job jpR jpL) fpR fpL
            (Hfp : JitFPRel fpR fpL) :
          PropSPropRel (@PDS.respects_FP_policy_at_preemption_point Task Job jtR ja'R costR PR jpR jrR arrR sR fpR)
            (I.Prosa_Model_Schedule_PriorityDriven_respects_FP_policy_at_preemption_point
              Task dT Job dJ jtL ja'L costL PL jpL jrL arrL sL fpL).
        Proof.
          unfold PDS.respects_FP_policy_at_preemption_point, PDS.respects_JLDP_policy_at_preemption_point.
          cbn [I.Prosa_Model_Schedule_PriorityDriven_respects_FP_policy_at_preemption_point
            I.Prosa_Model_Schedule_PriorityDriven_respects_JLDP_policy_at_preemption_point].
          apply ar_forall_identity_correspondence. intro j.
          apply ar_forall_identity_correspondence. intro j_hp.
          apply ar_forall_nat_correspondence. intros tR tL Ht.
          apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
          apply ar_imp_correspondence;
            [exact (ar_bool_truth_correspondence _ _
              (fpre_preemption_time_related Job PR PL X sR sL Hs arrR arrL Harr jpR jpL Hjp tR tL Ht))|].
          apply ar_imp_correspondence;
            [exact (ar_bool_truth_correspondence _ _ (jit_backlogged_related j tR tL Ht))|].
          apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hsa j_hp tR tL Ht))|].
          apply ar_bool_truth_correspondence. cbn.
          exact (sub_imported_eq_trans _ _ _ (Hfp _ _)
            (sub_imported_eq_congr2 (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fpL)
              _ _ _ _ (Hjt j_hp) (Hjt j))).
        Qed.
      End Arr.
    End Ready.

    Section Arr2.
      Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
      Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
      Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

      Lemma jit_scheduled_jobs_at_related tR tL (Ht : SubNatRel tR tL) :
        ArListRel (@prosa.model.schedule.scheduled.scheduled_jobs_at Job PR arrR sR tR)
          (I.Prosa_Model_Schedule_Scheduled_scheduled_jobs_at Job dJ PL arrL sL tL).
      Proof. exact (isj_scheduled_jobs_at_related Job PR PL sR sL Hsa arrR arrL Harr tR tL Ht). Qed.

      Lemma jit_scheduled_job_at_related tR tL (Ht : SubNatRel tR tL) :
        Lean.eq (jit_opt_to_imported (@prosa.model.schedule.scheduled.scheduled_job_at Job PR arrR sR tR))
          (I.Prosa_Model_Schedule_Scheduled_scheduled_job_at Job dJ PL arrL sL tL).
      Proof.
        unfold prosa.model.schedule.scheduled.scheduled_job_at.
        cbn [I.Prosa_Model_Schedule_Scheduled_scheduled_job_at].
        exact (jit_ohead_related _ _ (jit_scheduled_jobs_at_related tR tL Ht)).
      Qed.

      Lemma jit_response_time_bound_rel ja'R ja'L (Hja' : ArJobArrivalRel Job ja'R ja'L) tsk RR RL
          (HR : SubNatRel RR RL) :
        PropSPropRel (@SCH.task_response_time_bound Task Job ja'R costR jtR PR arrR sR tsk RR)
          (I.Prosa_Analysis_Definitions_Schedulability_task_response_time_bound
            Task dT Job dJ ja'L costL jtL PL arrL sL tsk RL).
      Proof.
        unfold SCH.task_response_time_bound, prosa.behavior.service.job_response_time_bound.
        cbn [I.Prosa_Analysis_Definitions_Schedulability_task_response_time_bound
          I.Prosa_Behavior_Service_job_response_time_bound].
        apply ar_forall_identity_correspondence. intro j.
        apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
        apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (jit_job_of_task_related tsk j))|].
        exact (ar_bool_truth_correspondence _ _ (fpre_completed_by_related Job costR costL Hcost PR PL X sR sL Hs j
          _ _ (svc_target_add_related _ _ _ _ (Hja' j) HR))).
      Qed.
    End Arr2.
  End Pair.

  (** *** The shared prefix *)

  Ltac jit_arr_ts arrR arrL Harr tsR tsL Hts :=
    apply fpre_forall_arr; intros arrR arrL Harr;
    (apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|]);
    apply jit_forall_list; intros tsR tsL Hts;
    (apply ar_imp_correspondence; [exact (jit_valid_jitter_bounds_rel tsR tsL Hts)|]).

  Ltac jit_pstate_sched PR PL X sR sL Hs :=
    apply (isj_cover_pstate Job); intros PR PL X;
    apply (fpre_forall_sched Job PR PL X); intros sR sL Hs.

  (** *** jitter_arrives_in_iff *)

  Definition src_jitter_arrives_in_iff : Prop :=
    ltac:(body_of (fun s : S.statement_jitter_arrives_in_iff => s Task Job jtR jaR tjR jjR)).
  Definition tgt_jitter_arrives_in_iff : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Jitter_jitter_arrives_in_iff Task dT Job dJ jtL jaL tjL jjL)).

  Theorem jitter_arrives_in_iff_correspondence :
    PropSPropRel src_jitter_arrives_in_iff tgt_jitter_arrives_in_iff.
  Proof.
    unfold src_jitter_arrives_in_iff, tgt_jitter_arrives_in_iff.
    jit_arr_ts arrR arrL Harr tsR tsL Hts.
    apply ar_forall_identity_correspondence. intro j.
    apply dp_iff_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    exact (arrives_in_correspondence_certificate Job _ _ j (jit_release_sequence_rel arrR arrL Harr)).
  Qed.

  (** *** valid_release_sequence *)

  Definition src_valid_release_sequence : Prop :=
    ltac:(body_of (fun s : S.statement_valid_release_sequence => s Task Job jtR jaR tjR jjR)).
  Definition tgt_valid_release_sequence : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Jitter_valid_release_sequence Task dT Job dJ jtL jaL tjL jjL)).

  Theorem valid_release_sequence_correspondence :
    PropSPropRel src_valid_release_sequence tgt_valid_release_sequence.
  Proof.
    unfold src_valid_release_sequence, tgt_valid_release_sequence.
    jit_arr_ts arrR arrL Harr tsR tsL Hts.
    exact (valid_arrival_sequence_correspondence_certificate Job relR relL _ _ jit_release_rel
      (jit_release_sequence_rel arrR arrL Harr)).
  Qed.

  (** *** valid_release_curve *)

  Definition src_valid_release_curve (maR : prosa.model.task.arrival.curves.MaxArrivals Task) : Prop :=
    ltac:(body_of (fun s : S.statement_valid_release_curve => s Task maR tjR)).
  Definition tgt_valid_release_curve (maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT) : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Jitter_valid_release_curve Task dT maL tjL)).

  Theorem valid_release_curve_correspondence maR maL (Hma : CvMaxArrivalsRel Task maR maL) :
    PropSPropRel (src_valid_release_curve maR) (tgt_valid_release_curve maL).
  Proof.
    unfold src_valid_release_curve, tgt_valid_release_curve.
    apply jit_forall_list. intros tsR tsL Hts.
    apply ar_imp_correspondence; [exact (valid_taskset_arrival_curve_correspondence Task tsR tsL _ _ Hts Hma)|].
    exact (valid_taskset_arrival_curve_correspondence Task tsR tsL _ _ Hts (jit_release_curve_rel maR maL Hma)).
  Qed.

  (** *** release_curve_respected *)

  Definition src_release_curve_respected (maR : prosa.model.task.arrival.curves.MaxArrivals Task) : Prop :=
    ltac:(body_of (fun s : S.statement_release_curve_respected => s Task maR Job jtR jaR tjR jjR)).
  Definition tgt_release_curve_respected (maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT) : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Jitter_release_curve_respected Task dT Job dJ maL jtL jaL tjL jjL)).

  Theorem release_curve_respected_correspondence maR maL (Hma : CvMaxArrivalsRel Task maR maL) :
    PropSPropRel (src_release_curve_respected maR) (tgt_release_curve_respected maL).
  Proof.
    unfold src_release_curve_respected, tgt_release_curve_respected.
    jit_arr_ts arrR arrL Harr tsR tsL Hts.
    apply ar_imp_correspondence; [exact (valid_taskset_arrival_curve_correspondence Task tsR tsL _ _ Hts Hma)|].
    apply ar_imp_correspondence;
      [exact (taskset_respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsR tsL Hts _ _ Hma)|].
    exact (taskset_respects_max_arrivals_correspondence Task Job jtR jtL Hjt _ _ (jit_release_sequence_rel arrR arrL Harr)
      tsR tsL Hts _ _ (jit_release_curve_rel maR maL Hma)).
  Qed.

  (** *** jitter_prop_same_jobs *)

  Definition src_jitter_prop_same_jobs : Prop :=
    ltac:(body_of (fun s : S.statement_jitter_prop_same_jobs => s Task Job jtR jaR tjR jjR)).
  Definition tgt_jitter_prop_same_jobs : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Jitter_jitter_prop_same_jobs Task dT Job dJ jtL jaL tjL jjL)).

  Theorem jitter_prop_same_jobs_correspondence :
    PropSPropRel src_jitter_prop_same_jobs tgt_jitter_prop_same_jobs.
  Proof.
    unfold src_jitter_prop_same_jobs, tgt_jitter_prop_same_jobs.
    jit_arr_ts arrR arrL Harr tsR tsL Hts.
    apply ar_imp_correspondence; [exact (jit_all_jobs_from_taskset_rel arrR arrL Harr tsR tsL Hts)|].
    exact (jit_all_jobs_from_taskset_rel _ _ (jit_release_sequence_rel arrR arrL Harr) tsR tsL Hts).
  Qed.

  (** *** jitter_prop_same_jobs' *)

  Definition src_jitter_prop_same_jobs' : Prop :=
    ltac:(body_of (fun s : S.statement_jitter_prop_same_jobs' => s Task Job jtR jaR tjR jjR)).
  Definition tgt_jitter_prop_same_jobs' : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Jitter_jitter_prop_same_jobs' Task dT Job dJ jtL jaL tjL jjL)).

  Theorem jitter_prop_same_jobs'_correspondence :
    PropSPropRel src_jitter_prop_same_jobs' tgt_jitter_prop_same_jobs'.
  Proof.
    unfold src_jitter_prop_same_jobs', tgt_jitter_prop_same_jobs'.
    jit_arr_ts arrR arrL Harr tsR tsL Hts.
    jit_pstate_sched PR PL X sR sL Hs.
    apply ar_imp_correspondence; [exact (fpre_come_from_rel Job PR PL X sR sL Hs arrR arrL Harr)|].
    exact (fpre_come_from_rel Job PR PL X sR sL Hs _ _ (jit_release_sequence_rel arrR arrL Harr)).
  Qed.

  (** *** jitter_prop_valid_costs *)

  Definition src_jitter_prop_valid_costs : Prop :=
    ltac:(body_of (fun s : S.statement_jitter_prop_valid_costs => s Task Job jtR jaR tjR jjR)).
  Definition tgt_jitter_prop_valid_costs : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Jitter_jitter_prop_valid_costs Task dT Job dJ jtL jaL tjL jjL)).

  Theorem jitter_prop_valid_costs_correspondence :
    PropSPropRel src_jitter_prop_valid_costs tgt_jitter_prop_valid_costs.
  Proof.
    unfold src_jitter_prop_valid_costs, tgt_jitter_prop_valid_costs.
    jit_arr_ts arrR arrL Harr tsR tsL Hts.
    apply jit_forall_job_cost. intros costR costL Hcost.
    apply jit_forall_task_cost. intros tcR tcL Htc.
    apply ar_imp_correspondence; [exact (jit_valid_job_costs_rel tcR tcL Htc costR costL Hcost arrR arrL Harr)|].
    exact (jit_valid_job_costs_rel tcR tcL Htc costR costL Hcost _ _ (jit_release_sequence_rel arrR arrL Harr)).
  Qed.

  (** *** jitter_ready_to_execute *)

  Definition src_jitter_ready_to_execute : Prop :=
    ltac:(body_of (fun s : S.statement_jitter_ready_to_execute => s Job jaR jjR)).
  Definition tgt_jitter_ready_to_execute : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Jitter_jitter_ready_to_execute Job dJ jaL jjL)).

  Theorem jitter_ready_to_execute_correspondence :
    PropSPropRel src_jitter_ready_to_execute tgt_jitter_ready_to_execute.
  Proof.
    unfold src_jitter_ready_to_execute, tgt_jitter_ready_to_execute.
    jit_pstate_sched PR PL X sR sL Hs.
    apply jit_forall_job_cost. intros costR costL Hcost.
    apply ar_imp_correspondence;
      [exact (jit_must_be_ready_rel PR PL X sR sL Hs costR costL _ _ _ _ (jit_jitter_ready_rel PR PL X sR sL Hs costR costL Hcost))|].
    exact (jit_must_be_ready_rel PR PL X sR sL Hs costR costL _ _ _ _ (jit_basic_ready_rel PR PL X sR sL Hs costR costL Hcost)).
  Qed.

  (** *** The statements over a valid schedule *)

  Ltac jit_sched_cost PR PL X sR sL Hs costR costL Hcost :=
    jit_pstate_sched PR PL X sR sL Hs;
    apply jit_forall_job_cost; intros costR costL Hcost.

  Definition src_jitter_work_conservation : Prop :=
    ltac:(body_of (fun s : S.statement_jitter_work_conservation => s Task Job jtR jaR tjR jjR)).
  Definition tgt_jitter_work_conservation : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Jitter_jitter_work_conservation Task dT Job dJ jtL jaL tjL jjL)).

  Theorem jitter_work_conservation_correspondence :
    PropSPropRel src_jitter_work_conservation tgt_jitter_work_conservation.
  Proof.
    unfold src_jitter_work_conservation, tgt_jitter_work_conservation.
    jit_arr_ts arrR arrL Harr tsR tsL Hts.
    jit_sched_cost PR PL X sR sL Hs costR costL Hcost.
    apply ar_imp_correspondence;
      [exact (jit_work_conserving_rel PR PL X sR sL Hs costR costL _ _ _ _
        (jit_jitter_ready_rel PR PL X sR sL Hs costR costL Hcost) arrR arrL Harr)|].
    exact (jit_work_conserving_rel PR PL X sR sL Hs costR costL _ _ _ _
      (jit_basic_ready_rel PR PL X sR sL Hs costR costL Hcost) _ _ (jit_release_sequence_rel arrR arrL Harr)).
  Qed.

  Definition src_jitter_valid_schedule : Prop :=
    ltac:(body_of (fun s : S.statement_jitter_valid_schedule => s Task Job jtR jaR tjR jjR)).
  Definition tgt_jitter_valid_schedule : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Jitter_jitter_valid_schedule Task dT Job dJ jtL jaL tjL jjL)).

  Theorem jitter_valid_schedule_correspondence :
    PropSPropRel src_jitter_valid_schedule tgt_jitter_valid_schedule.
  Proof.
    unfold src_jitter_valid_schedule, tgt_jitter_valid_schedule.
    jit_arr_ts arrR arrL Harr tsR tsL Hts.
    jit_sched_cost PR PL X sR sL Hs costR costL Hcost.
    apply ar_imp_correspondence;
      [exact (jit_valid_schedule_rel PR PL X sR sL Hs costR costL _ _ _ _
        (jit_jitter_ready_rel PR PL X sR sL Hs costR costL Hcost) arrR arrL Harr)|].
    exact (jit_valid_schedule_rel PR PL X sR sL Hs costR costL _ _ _ _
      (jit_basic_ready_rel PR PL X sR sL Hs costR costL Hcost) _ _ (jit_release_sequence_rel arrR arrL Harr)).
  Qed.

  Ltac jit_valid_prefix arrR arrL Harr PR PL X sR sL Hs costR costL Hcost :=
    (apply ar_imp_correspondence;
      [exact (jit_valid_schedule_rel PR PL X sR sL Hs costR costL _ _ _ _
        (jit_jitter_ready_rel PR PL X sR sL Hs costR costL Hcost) arrR arrL Harr)|]).

  Definition src_jitter_scheduled_jobs_at_equiv : Prop :=
    ltac:(body_of (fun s : S.statement_jitter_scheduled_jobs_at_equiv => s Task Job jtR jaR tjR jjR)).
  Definition tgt_jitter_scheduled_jobs_at_equiv : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Jitter_jitter_scheduled_jobs_at_equiv Task dT Job dJ jtL jaL tjL jjL)).

  Theorem jitter_scheduled_jobs_at_equiv_correspondence :
    PropSPropRel src_jitter_scheduled_jobs_at_equiv tgt_jitter_scheduled_jobs_at_equiv.
  Proof.
    unfold src_jitter_scheduled_jobs_at_equiv, tgt_jitter_scheduled_jobs_at_equiv.
    jit_arr_ts arrR arrL Harr tsR tsL Hts.
    jit_sched_cost PR PL X sR sL Hs costR costL Hcost.
    jit_valid_prefix arrR arrL Harr PR PL X sR sL Hs costR costL Hcost.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_bool_eq_correspondence.
    - exact (ar_decide_mem_related Job j _ _
        (jit_scheduled_jobs_at_related PR PL X sR sL Hs _ _ (jit_release_sequence_rel arrR arrL Harr) tR tL Ht)).
    - exact (ar_decide_mem_related Job j _ _ (jit_scheduled_jobs_at_related PR PL X sR sL Hs arrR arrL Harr tR tL Ht)).
  Qed.

  Definition src_jitter_scheduled_job_at_eq : Prop :=
    ltac:(body_of (fun s : S.statement_jitter_scheduled_job_at_eq => s Task Job jtR jaR tjR jjR)).
  Definition tgt_jitter_scheduled_job_at_eq : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Jitter_jitter_scheduled_job_at_eq Task dT Job dJ jtL jaL tjL jjL)).

  Theorem jitter_scheduled_job_at_eq_correspondence :
    PropSPropRel src_jitter_scheduled_job_at_eq tgt_jitter_scheduled_job_at_eq.
  Proof.
    unfold src_jitter_scheduled_job_at_eq, tgt_jitter_scheduled_job_at_eq.
    jit_arr_ts arrR arrL Harr tsR tsL Hts.
    jit_sched_cost PR PL X sR sL Hs costR costL Hcost.
    jit_valid_prefix arrR arrL Harr PR PL X sR sL Hs costR costL Hcost.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (isj_psr_uniprocessor_related Job PR PL X)|].
    exact (jit_opt_eq_correspondence _ _ _ _ (jit_scheduled_job_at_related PR PL X sR sL Hs arrR arrL Harr tR tL Ht)
      (jit_scheduled_job_at_related PR PL X sR sL Hs _ _ (jit_release_sequence_rel arrR arrL Harr) tR tL Ht)).
  Qed.

  Definition src_jitter_FP_compliance : Prop :=
    ltac:(body_of (fun s : S.statement_jitter_FP_compliance => s Task Job jtR jaR tjR jjR)).
  Definition tgt_jitter_FP_compliance : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Jitter_jitter_FP_compliance Task dT Job dJ jtL jaL tjL jjL)).

  Theorem jitter_FP_compliance_correspondence :
    PropSPropRel src_jitter_FP_compliance tgt_jitter_FP_compliance.
  Proof.
    unfold src_jitter_FP_compliance, tgt_jitter_FP_compliance.
    jit_arr_ts arrR arrL Harr tsR tsL Hts.
    jit_sched_cost PR PL X sR sL Hs costR costL Hcost.
    jit_valid_prefix arrR arrL Harr PR PL X sR sL Hs costR costL Hcost.
    apply jit_forall_fp. intros fpR fpL Hfp.
    apply (fpre_forall_jp Job). intros jpR jpL Hjp.
    apply ar_imp_correspondence; [exact (isj_psr_uniprocessor_related Job PR PL X)|].
    apply ar_imp_correspondence;
      [exact (jit_respects_fp_rel PR PL X sR sL Hs costR costL _ _ _ _
        (jit_jitter_ready_rel PR PL X sR sL Hs costR costL Hcost) arrR arrL Harr jpR jpL Hjp fpR fpL Hfp)|].
    exact (jit_respects_fp_rel PR PL X sR sL Hs costR costL _ _ _ _
      (jit_basic_ready_rel PR PL X sR sL Hs costR costL Hcost) _ _ (jit_release_sequence_rel arrR arrL Harr)
      jpR jpL Hjp fpR fpL Hfp).
  Qed.

  Definition src_jitter_response_time_bound : Prop :=
    ltac:(body_of (fun s : S.statement_jitter_response_time_bound => s Task Job jtR jaR tjR jjR)).
  Definition tgt_jitter_response_time_bound : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Jitter_jitter_response_time_bound Task dT Job dJ jtL jaL tjL jjL)).

  Theorem jitter_response_time_bound_correspondence :
    PropSPropRel src_jitter_response_time_bound tgt_jitter_response_time_bound.
  Proof.
    unfold src_jitter_response_time_bound, tgt_jitter_response_time_bound.
    jit_arr_ts arrR arrL Harr tsR tsL Hts.
    jit_sched_cost PR PL X sR sL Hs costR costL Hcost.
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_forall_nat_correspondence. intros RR RL HR.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts))|].
    apply ar_imp_correspondence;
      [exact (jit_response_time_bound_rel PR PL X sR sL Hs costR costL Hcost _ _
        (jit_release_sequence_rel arrR arrL Harr) relR relL jit_release_rel tsk RR RL HR)|].
    exact (jit_response_time_bound_rel PR PL X sR sL Hs costR costL Hcost arrR arrL Harr jaR jaL Hja tsk _ _
      (svc_target_add_related _ _ _ _ (Htj tsk) HR)).
  Qed.

End Jitter.
