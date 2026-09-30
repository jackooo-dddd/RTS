From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import RtaExcFpFullyNonpreemptiveSemanticSource.
From prosa Require Import behavior.all model.processor.ideal_uni_exceed analysis.facts.model.ideal_uni_exceed
  model.readiness.sequential model.preemption.fully_nonpreemptive model.schedule.nonpreemptive
  model.task.sequentiality model.task.arrival.curves model.job.properties model.composite.valid_task_arrival_sequence.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRtaExcFpFullyNonpreemptive ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ExcArrivalsSeqBaseAdapter ExcArrivalsSeqOperations ExcArrivalsSeqCorrespondence ExcArrivalsCorrespondence
  ExcJitterSvcBaseAdapter ExcJitterSvcNatBoolOperations ExcJitterSvcIntervalOperations
  ExcJitterSvcScheduleOperations ExcJitterSvcJobOperations ExcPreemptionParameterCorrespondence
  ExcPreemptionTimeCorrespondence ExcPriorityDrivenCorrespondence ExcPStateCoverHelpers ExcFactsPreemptionHelpers
  ExcWorkloadCorrespondence ExcPriorityInversionCorrespondence ExcExistenceHelpers ExcHepAtPtHelpers
  ExcTaskPreemptionParametersCorrespondence ExcBusyIntervalPiHelpers ExcStateRel ExcCurvesCorrespondence.
From FoundationCertificates Require ExcRequestBoundFunctionCorrespondence ExcBlockingBoundFpCorrespondence
  ExcSearchSpaceFpCorrespondence.

Module I := ImportedRtaExcFpFullyNonpreemptive.
Module S := RtaExcFpFullyNonpreemptiveSemanticSource.RtaExcFpFullyNonpreemptiveSemanticSource.
Module SCH := SchedulabilitySemanticSource.SchedulabilitySemanticSource.
Module RBF := ExcRequestBoundFunctionCorrespondence.
Module SSF := ExcSearchSpaceFpCorrespondence.
Module BBF := ExcBlockingBoundFpCorrespondence.
Module TFN := TaskPreemptionFullyNonpreemptiveSemanticSource.TaskPreemptionFullyNonpreemptiveSemanticSource.

(** Definition and statement correspondences for [results/rta/exc/fp/fully_nonpreemptive.v].

    Source side: the extracted definitions and statement specialised at their leading input binders; target
    side: the compiled Lean definitions and the imported Lean theorem type.  Leading inputs: the task and job
    types, the task-cost, arrival-curve, job-task, job-cost and job-arrival instances, related by the accepted
    relations (tasks and jobs by identity).  The exceedance processor model is fixed on both sides and related by
    [exc_psrel] (ExcStateRel.v); the generic chain helpers are replayed at its universe instance (Exc*.v, see
    their headers).  Task sets, FP policies (pointwise on Booleans, two-way totals), arrival sequences and
    schedules are covered in both directions; the exceedance budget and the busy-window, response-time, offset and
    fixpoint values are related by [SubNatRel].  [task_request_bound_function], the higher-or-equal and
    other-higher-or-equal priority RBFs, the FP [blocking_bound] (at the fully nonpreemptive task model, related
    pointwise through [task_cost]) and the FP [is_in_search_space] are the accepted definition certificates
    re-bound to this export and to the replayed arrivals modules; [valid_task_arrival_sequence] unfolds into the
    accepted arrival-sequence, job-cost, task-set and arrival-curve relations; [FP_to_JLFP] is related as a JLFP
    policy through [job_task]; task-priority reflexivity and transitivity pointwise; the fully nonpreemptive job
    model pointwise through [job_cost]; [nonpreemptive_schedule] unfolds over the accepted scheduled and completion
    relations at the schedule pair; the source-local sequential readiness instance is related pointwise at the
    schedule pair through the accepted [pending] relation and [prior_jobs_complete] (the accepted
    [task_arrivals_before] and [completed_by] relations); the exceedance hypothesis through the accepted classical
    busy-interval-prefix relation, the accepted interval-sum and [nat_of_bool] relations and [is_exceedance_exec]
    constructor-wise.  No source or target theorem is used. *)

Local Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Local Ltac type_of_term t := let T := type of t in exact T.

(** MathComp [all] versus Lean [List.all]. *)
Lemma rexc_all_canonical (T : Type) (pR : T -> bool) (pL : T -> I.Bool) :
  (forall x, ArBoolRel (pR x) (pL x)) ->
  forall xs : seq T, ArBoolRel (all pR xs) (I.List_all T (ar_list_to_imported xs) pL).
Proof.
  intros Hp xs. induction xs as [|x xs IH].
  - exact (@Lean.eq_refl _ _).
  - exact (ar_bool_and_related _ _ _ _ (Hp x) IH).
Qed.

Lemma rexc_all_related (T : Type) (pR : T -> bool) (pL : T -> I.Bool) xsR xsL :
  (forall x, ArBoolRel (pR x) (pL x)) -> ArListRel xsR xsL ->
  ArBoolRel (all pR xsR) (I.List_all T xsL pL).
Proof.
  intros Hp Hxs.
  refine (isj_lean_transport (fun l => ArBoolRel (all pR xsR) (I.List_all T l pL)) _ _ Hxs _).
  exact (rexc_all_canonical T pR pL Hp xsR).
Qed.

Section Rta.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
  Let PR := prosa.model.processor.ideal_uni_exceed.exceedance_proc_state Job.
  Let PL := I.Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state Job dJ.
  Let X := exc_psrel Job.
  Variable tcR : prosa.model.task.concept.TaskCost Task.
  Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
  Hypothesis Htc : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).
  Variable maR : prosa.model.task.arrival.curves.MaxArrivals Task.
  Variable maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT.
  Hypothesis Hma : CvMaxArrivalsRel Task maR maL.
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

  Local Ltac imp H := apply ar_imp_correspondence; [exact H|].

  (** *** Task-level relations *)

  Lemma rexc_task_cost_of_job_related (j : Job) :
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

    Lemma rexc_valid_job_costs_rel :
      PropSPropRel (@prosa.model.task.concept.arrivals_have_valid_job_costs Task tcR Job jtR costR arrR)
        (I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task dT tcL Job dJ jtL costL arrL).
    Proof.
      unfold prosa.model.task.concept.arrivals_have_valid_job_costs, prosa.model.task.concept.valid_job_cost.
      cbn [I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs I.Prosa_Model_Task_Concept_valid_job_cost].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
      exact (ar_bool_truth_correspondence _ _
        (svc_decide_le_related _ _ _ _ (Hcost j) (rexc_task_cost_of_job_related j))).
    Qed.

    Lemma rexc_all_jobs_from_taskset_rel tsR tsL (Hts : ArListRel tsR tsL) :
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

    Lemma rexc_valid_task_arrival_sequence_rel tsR tsL (Hts : ArListRel tsR tsL) :
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
      apply ar_and_correspondence; [exact rexc_valid_job_costs_rel|].
      apply ar_and_correspondence; [exact (rexc_all_jobs_from_taskset_rel tsR tsL Hts)|].
      apply ar_and_correspondence.
      - exact (taskset_respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsR tsL Hts
          maR maL Hma).
      - exact (valid_taskset_arrival_curve_correspondence Task tsR tsL _ _ Hts Hma).
    Qed.

    Lemma rexc_positive_costs_rel :
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

  Section Pair.
    Variable sR : @prosa.behavior.schedule.schedule Job PR.
    Variable sL : I.Prosa_Behavior_Schedule_schedule_inst4 Job dJ PL.
    Hypothesis Hs : IsjPSchedRel Job PR PL X sR sL.
    Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
    Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
    Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

    Lemma rexc_prior_jobs_complete_related (j : Job) tR tL (Ht : SubNatRel tR tL) :
      ArBoolRel (@prosa.model.task.sequentiality.prior_jobs_complete Job Task jtR jaR costR PR arrR sR j tR)
        (I.Prosa_Model_Task_Sequentiality_prior_jobs_complete_inst8 Job dJ Task dT jtL jaL costL PL arrL sL j tL).
    Proof.
      unfold prosa.model.task.sequentiality.prior_jobs_complete.
      cbn [I.Prosa_Model_Task_Sequentiality_prior_jobs_complete_inst8].
      apply rexc_all_related.
      - intro x. exact (fpre_completed_by_related Job costR costL Hcost PR PL X sR sL Hs x tR tL Ht).
      - exact (task_arrivals_before_correspondence Job Task jtR jtL Hjt arrR arrL Harr _ _ _ _ (Hjt j) (Hja j)).
    Qed.

    Lemma rexc_sequential_ready_rel :
      FpreJrAt Job jaR jaL costR costL PR PL sR sL
        (@S.sequential_readiness Task Job jtR costR jaR arrR)
        (I.Prosa_Model_Readiness_Sequential_sequential_ready_instance_inst8 Job dJ Task dT jtL jaL costL PL arrL).
    Proof.
      intros j tR tL Ht.
      unfold S.sequential_readiness. cbn.
      apply ar_bool_and_related.
      - exact (fpre_pending_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs j tR tL Ht).
      - exact (rexc_prior_jobs_complete_related j tR tL Ht).
    Qed.

    Lemma rexc_is_exceedance_exec_related tR tL :
      SubNatRel tR tL ->
      SvcBoolRel (@prosa.analysis.facts.model.ideal_uni_exceed.is_exceedance_exec Job (sR tR))
        (I.Prosa_Analysis_Facts_Model_IdealUniExceed_is_exceedance_exec Job dJ (sL tL)).
    Proof.
      intro Ht.
      refine (isj_lean_transport
        (fun s => SvcBoolRel (@prosa.analysis.facts.model.ideal_uni_exceed.is_exceedance_exec Job (sR tR))
           (I.Prosa_Analysis_Facts_Model_IdealUniExceed_is_exceedance_exec Job dJ s))
        _ _ (Hs tR tL Ht) _).
      cbn. destruct (sR tR); exact (@Lean.eq_refl _ _).
    Qed.
  End Pair.

  Definition RexcFPRel (pR : prosa.model.priority.definitions.FP_policy Task)
      (pL : I.Prosa_Model_Priority_Definitions_FP_policy Task dT) : SProp :=
    forall x y : Task,
      ArBoolRel (@prosa.model.priority.definitions.hep_task Task pR x y)
        (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT pL x y).

  Lemma rexc_forall_fp (P : prosa.model.priority.definitions.FP_policy Task -> Prop)
      (Q : I.Prosa_Model_Priority_Definitions_FP_policy Task dT -> SProp) :
    (forall a b, RexcFPRel a b -> PropSPropRel (P a) (Q b)) ->
    PropSPropRel (forall a, P a) (forall b, Q b).
  Proof.
    apply (isj_forall_cover_sprop _ _ RexcFPRel
      (fun pR => I.Prosa_Model_Priority_Definitions_FP_policy_mk Task dT
        (fun x y => ar_bool_to_imported (@prosa.model.priority.definitions.hep_task Task pR x y)))
      (fun pL => (fun x y => ar_bool_to_rocq (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT pL x y))
        : prosa.model.priority.definitions.FP_policy Task)).
    - intros pR x y. exact (@Lean.eq_refl _ _).
    - intros pL x y. exact (ar_bool_target_roundtrip _).
  Qed.

  Lemma rexc_reflexive_task_rel fR fL (Hf : RexcFPRel fR fL) :
    PropSPropRel (@prosa.model.priority.definitions.reflexive_task_priorities Task fR)
      (I.Prosa_Model_Priority_Definitions_reflexive_task_priorities Task dT fL).
  Proof.
    unfold prosa.model.priority.definitions.reflexive_task_priorities.
    cbn [I.Prosa_Model_Priority_Definitions_reflexive_task_priorities].
    apply ar_forall_identity_correspondence. intro tsk.
    exact (ar_bool_truth_correspondence _ _ (Hf tsk tsk)).
  Qed.

  Lemma rexc_transitive_task_rel fR fL (Hf : RexcFPRel fR fL) :
    PropSPropRel (@prosa.model.priority.definitions.transitive_task_priorities Task fR)
      (I.Prosa_Model_Priority_Definitions_transitive_task_priorities Task dT fL).
  Proof.
    unfold prosa.model.priority.definitions.transitive_task_priorities.
    cbn [I.Prosa_Model_Priority_Definitions_transitive_task_priorities].
    apply ar_forall_identity_correspondence. intro y.
    apply ar_forall_identity_correspondence. intro x.
    apply ar_forall_identity_correspondence. intro z.
    apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hf x y))|].
    apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hf y z))|].
    exact (ar_bool_truth_correspondence _ _ (Hf x z)).
  Qed.

  Lemma rexc_fp_hep_job_related fR fL (Hf : RexcFPRel fR fL) :
    FpreJLFPRel Job (@prosa.model.priority.coercion.FP_to_JLFP Job Task jtR fR)
      (I.Prosa_Model_Priority_Coercion_FP_to_JLFP Job dJ Task dT jtL fL).
  Proof.
    intros x y.
    change (ArBoolRel (@prosa.model.priority.definitions.hep_task Task fR
        (@prosa.model.task.concept.job_task Job Task jtR x) (@prosa.model.task.concept.job_task Job Task jtR y))
      (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL x)
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL y))).
    refine (isj_lean_transport (fun v => ArBoolRel _
      (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fL v
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL y))) _ _ (Hjt x) _).
    refine (isj_lean_transport (fun v => ArBoolRel _
      (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fL
        (@prosa.model.task.concept.job_task Job Task jtR x) v)) _ _ (Hjt y) _).
    exact (Hf _ _).
  Qed.


  Lemma rexc_task_model_related :
    TppMaxSegmentRel Task (@TFN.fully_nonpreemptive_task_model Task tcR)
      (I.Prosa_Model_Task_Preemption_FullyNonpreemptive_fully_nonpreemptive_task_model Task dT tcL).
  Proof. intro tsk. exact (Htc tsk). Qed.

  Lemma rexc_job_model_related :
    PpJobPreemptableRel Job
      (@prosa.model.preemption.fully_nonpreemptive.fully_nonpreemptive_job_model Job costR)
      (I.Prosa_Model_Preemption_FullyNonpreemptive_fully_nonpreemptive_job_model Job dJ costL).
  Proof.
    intros j nR nL Hn.
    exact (pp_bool_or_related _ _ _ _
      (pp_nat_eqb_related _ _ _ _ Hn (sub_nat_rel_canonical O))
      (pp_nat_eqb_related _ _ _ _ Hn (Hcost j))).
  Qed.

  Lemma rexc_nonpreemptive_schedule_rel sR sL (Hs : IsjPSchedRel Job PR PL X sR sL) :
    PropSPropRel (@prosa.model.schedule.nonpreemptive.nonpreemptive_schedule Job costR PR sR)
      (I.Prosa_Model_Schedule_Nonpreemptive_nonpreemptive_schedule_inst4 Job dJ costL PL sL).
  Proof.
    unfold prosa.model.schedule.nonpreemptive.nonpreemptive_schedule.
    cbn [I.Prosa_Model_Schedule_Nonpreemptive_nonpreemptive_schedule_inst4].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_forall_nat_correspondence. intros tR' tL' Ht'.
    imp (sub_nat_le_correspondence _ _ _ _ Ht Ht').
    imp (ar_bool_truth_correspondence _ _ (isj_psr_scheduled_at_related Job PR PL X sR sL Hs j _ _ Ht)).
    imp (ar_bool_truth_correspondence _ _
      (svc_bool_not_related _ _ (fpre_completed_by_related Job costR costL Hcost PR PL X sR sL Hs j _ _ Ht'))).
    exact (ar_bool_truth_correspondence _ _ (isj_psr_scheduled_at_related Job PR PL X sR sL Hs j _ _ Ht')).
  Qed.

  Lemma rexc_job_of_task_related (tsk : Task) (j : Job) :
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

  (** *** The two definitions *)

  Section Defs.
    Variable tsR : seq Task.
    Variable tsL : I.List Task.
    Hypothesis Hts : ArListRel tsR tsL.
    Variable fR : prosa.model.priority.definitions.FP_policy Task.
    Variable fL : I.Prosa_Model_Priority_Definitions_FP_policy Task dT.
    Hypothesis Hf : RexcFPRel fR fL.
    Variables (eR : nat) (eL : Lean.Nat).
    Hypothesis He : SubNatRel eR eL.
    Variable tsk : Task.

    Let ONE := sub_nat_rel_canonical (S O).
    Let TSK tsk := RBF.task_request_bound_function_correspondence Task tcR tcL Htc maR maL Hma tsk.
    Let HEP dR dL (Hd : SubNatRel dR dL) :=
      RBF.total_hep_request_bound_function_FP_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts fR fL Hf
        tsk dR dL Hd.
    Let OHEP dR dL (Hd : SubNatRel dR dL) :=
      RBF.total_ohep_request_bound_function_FP_correspondence Task tcR tcL Htc maR maL Hma tsR tsL Hts fR fL Hf
        tsk dR dL Hd.
    Let BB := BBF.blocking_bound_correspondence Task _ _ rexc_task_model_related fR fL Hf tsR tsL Hts tsk.

    Theorem busy_window_recurrence_solution_correspondence (LR : nat) (LL : Lean.Nat) (HL : SubNatRel LR LL) :
      PropSPropRel (@S.busy_window_recurrence_solution Task tcR maR tsR fR eR tsk LR)
        (I.Prosa_Results_Rta_Exc_Fp_FullyNonpreemptive_busy_window_recurrence_solution
          Task dT tcL maL tsL fL eL tsk LL).
    Proof.
      unfold S.busy_window_recurrence_solution.
      cbn [I.Prosa_Results_Rta_Exc_Fp_FullyNonpreemptive_busy_window_recurrence_solution].
      apply ar_and_correspondence.
      - exact (sub_nat_lt_correspondence _ _ _ _ He HL).
      - exact (sub_nat_le_correspondence _ _ _ _
          (sub_add_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ BB (HEP _ _ HL)) He) HL).
    Qed.

    Theorem rta_recurrence_solution_correspondence (LR : nat) (LL : Lean.Nat) (HL : SubNatRel LR LL)
        (RR : nat) (RL : Lean.Nat) (HR : SubNatRel RR RL) :
      PropSPropRel (@S.rta_recurrence_solution Task tcR maR tsR fR eR tsk LR RR)
        (I.Prosa_Results_Rta_Exc_Fp_FullyNonpreemptive_rta_recurrence_solution
          Task dT tcL maL tsL fL eL tsk LL RL).
    Proof.
      unfold S.rta_recurrence_solution.
      cbn [I.Prosa_Results_Rta_Exc_Fp_FullyNonpreemptive_rta_recurrence_solution].
      apply ar_forall_nat_correspondence. intros AR AL HA.
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _
          (SSF.is_in_search_space_correspondence Task tcR tcL Htc maR maL Hma tsk LR AR LL AL HL HA))|].
      apply ar_exists_nat_correspondence. intros FR' FL' HF.
      have Hc1 := svc_target_sub_related _ _ _ _ (Htc tsk) ONE.
      apply ar_and_correspondence.
      - exact (sub_nat_le_correspondence _ _ _ _
          (sub_add_correspondence _ _ _ _
            (sub_add_correspondence _ _ _ _
              (sub_add_correspondence _ _ _ _ BB
                (svc_target_sub_related _ _ _ _ (TSK tsk _ _ (svc_target_add_related _ _ _ _ HA ONE)) Hc1))
              (OHEP _ _ HF))
            He)
          HF).
      - exact (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ HF Hc1)
          (svc_target_add_related _ _ _ _ HA HR)).
    Qed.
  End Defs.

  (** *** The theorem *)

  Definition src_uniprocessor_response_time_bound_fully_nonpreemptive_fp : Prop :=
    ltac:(body_of (fun s : S.statement_uniprocessor_response_time_bound_fully_nonpreemptive_fp =>
      s Task tcR maR Job jtR costR jaR)).
  Definition tgt_uniprocessor_response_time_bound_fully_nonpreemptive_fp : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Results_Rta_Exc_Fp_FullyNonpreemptive_uniprocessor_response_time_bound_fully_nonpreemptive_fp
        Task dT tcL maL Job dJ jtL costL jaL)).

  Theorem uniprocessor_response_time_bound_fully_nonpreemptive_fp_correspondence :
    PropSPropRel src_uniprocessor_response_time_bound_fully_nonpreemptive_fp
      tgt_uniprocessor_response_time_bound_fully_nonpreemptive_fp.
  Proof.
    unfold src_uniprocessor_response_time_bound_fully_nonpreemptive_fp,
      tgt_uniprocessor_response_time_bound_fully_nonpreemptive_fp.
    apply (fpre_forall_arr Job). intros arrR arrL Harr.
    apply (isj_forall_cover_sprop _ _ ArListRel ar_list_to_imported ar_list_to_rocq
      (fun xs => @Lean.eq_refl _ _) (fun xs => ar_list_target_roundtrip xs)).
    intros tsR tsL Hts.
    imp (rexc_valid_task_arrival_sequence_rel arrR arrL Harr tsR tsL Hts).
    apply (fpre_forall_sched Job PR PL X). intros sR sL Hs.
    have Hjr := rexc_sequential_ready_rel sR sL Hs arrR arrL Harr.
    imp (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr _ _ Hjr).
    imp (ex_work_conserving_related Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr _ _ Hjr).
    imp (rexc_nonpreemptive_schedule_rel sR sL Hs).
    apply rexc_forall_fp. intros fR fL Hf.
    imp (rexc_reflexive_task_rel fR fL Hf).
    imp (rexc_transitive_task_rel fR fL Hf).
    have Hp := rexc_fp_hep_job_related fR fL Hf.
    imp (fpre_respects_jlfp_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr _ _ Hjr
      _ _ rexc_job_model_related _ _ Hp).
    apply ar_forall_nat_correspondence. intros eR eL He.
    apply ar_forall_identity_correspondence. intro tsk.
    imp (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task tsk _ _ Hts)).
    apply ar_imp_correspondence.
    { apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros t1R t1L H1.
      apply ar_forall_nat_correspondence. intros t2R t2L H2.
      imp (arrives_in_correspondence_certificate Job arrR arrL j Harr).
      imp (ar_bool_truth_correspondence _ _ (rexc_job_of_task_related tsk j)).
      imp (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr
        _ _ Hp j t1R t1L t2R t2L H1 H2).
      refine (sub_nat_le_correspondence _ _ _ _ _ He).
      apply svc_interval_sum_related; [exact H1|exact H2|].
      intros tR tL Ht. exact (isj_bool_to_nat_related _ _ (rexc_is_exceedance_exec_related sR sL Hs tR tL Ht)). }
    apply ar_forall_nat_correspondence. intros LR LL HL.
    imp (busy_window_recurrence_solution_correspondence tsR tsL Hts fR fL Hf eR eL He tsk LR LL HL).
    apply ar_forall_nat_correspondence. intros RR RL HR.
    imp (rta_recurrence_solution_correspondence tsR tsL Hts fR fL Hf eR eL He tsk LR LL HL RR RL HR).
    unfold SCH.task_response_time_bound.
    cbn [I.Prosa_Analysis_Definitions_Schedulability_task_response_time_bound_inst8].
    apply ar_forall_identity_correspondence. intro j.
    imp (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    imp (ar_bool_truth_correspondence _ _ (rexc_job_of_task_related tsk j)).
    unfold prosa.behavior.service.job_response_time_bound.
    cbn [I.Prosa_Behavior_Service_job_response_time_bound_inst4].
    exact (ar_bool_truth_correspondence _ _
      (fpre_completed_by_related Job costR costL Hcost PR PL X sR sL Hs j _ _
        (svc_target_add_related _ _ _ _ (Hja j) HR))).
  Qed.
End Rta.
