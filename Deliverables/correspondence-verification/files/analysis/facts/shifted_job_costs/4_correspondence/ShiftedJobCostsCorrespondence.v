From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq div.
From prosa Require Import ShiftedJobCostsSemanticSource.
From prosa Require Import model.task.arrivals model.task.concept analysis.definitions.infinite_jobs.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedShiftedJobCosts ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  TaskOffsetCorrespondence PeriodicCorrespondence
  NatSubCorrespondence LcmseqBaseAdapter LcmseqDivModAdapter LcmseqCorrespondence
  HyperperiodCorrespondence InfiniteJobsCorrespondence.

Module I := ImportedShiftedJobCosts.
Module S := ShiftedJobCostsSemanticSource.ShiftedJobCostsSemanticSource.
Module O := TaskOffsetSemanticSource.TaskOffsetSemanticSource.
Module P := PeriodicSemanticSource.PeriodicSemanticSource.

(** Correspondences for [analysis/facts/shifted_job_costs.v].

    Inputs: task-offset, periodic-model, task-cost, job-task ([Lean.eq]),
    job-arrival, job-cost and arrival-sequence inputs by the accepted
    relations; tasks and jobs are identity carriers; task sets by the
    canonical list relation (covered in both directions inside the statement).
    [job_costs_shifted]: the Boolean condition is related through the
    accepted [&&], [<=] and [<] relations and the accepted Nat addition,
    multiplication and hyperperiod relations; the branches through the
    accepted [corresponding_job_in_hyperperiod] relation (jobs related by
    [Lean.eq]) and the job-cost relation; the source [if] and the Lean [cond]
    by case analysis on the related Booleans.  [job_costs_in_oi] is related
    pointwise as a job-cost instance.  The statement relates the job-cost
    validity of both instances, the periodic task set, periods, offsets,
    [infinite_jobs] and [all_jobs_from_taskset] through the accepted
    certificates.  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma sjc_forall_list_correspondence (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall xsR xsL, ArListRel xsR xsL -> PropSPropRel (PR xsR) (PL xsL)) ->
  PropSPropRel (forall xs, PR xs) (forall xs, PL xs).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros HR xsL.
    exact (prop_to_sprop _ _ (HP (ar_list_to_rocq xsL) xsL (ar_list_target_roundtrip xsL))
      (HR (ar_list_to_rocq xsL))).
  - intro HL. apply strictly_inhabits. intro xsR.
    exact (sprop_to_prop _ _ (HP xsR (ar_list_to_imported xsR) (@Lean.eq_refl _ _))
      (HL (ar_list_to_imported xsR))).
Qed.

Lemma sjc_cond_related (bR : bool) (bL : I.Bool) xR xL yR yL :
  ArBoolRel bR bL -> SubNatRel xR xL -> SubNatRel yR yL ->
  SubNatRel (if bR then xR else yR) (I.cond Lean.Nat bL xL yL).
Proof.
  intros Hb Hx Hy. destruct bR, bL; cbn in *;
    try exact Hx; try exact Hy;
    try exact (ar_false_elim _ (ar_false_ne_true Hb));
    try exact (ar_false_elim _ (ar_false_ne_true (sub_imported_eq_sym _ _ Hb))).
Qed.

Section ShiftedJobCosts.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
  Variable oR : O.TaskOffset Task.
  Variable oL : I.Prosa_Model_Task_Offset_TaskOffset Task dT.
  Hypothesis Hoff : OffRel Task oR oL.
  Variable pR : P.PeriodicModel Task.
  Variable pL : I.Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task dT.
  Hypothesis Hp : PerRel Task pR pL.
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
  Hypothesis Hcost : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_cost Job costR j) (I.Prosa_Behavior_Job_JobCost_job_cost Job dJ costL j).
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Section TaskSet.
    Variable tsR : seq Task.
    Variable tsL : I.List Task.
    Hypothesis Hts : ArListRel tsR tsL.

    Let HP := hyperperiod_correspondence Task pR pL Hp tsR tsL Hts.
    Let OMAX := max_task_offset_correspondence Task oR oL Hoff tsR tsL Hts.

    Theorem job_costs_shifted_correspondence (j j' : Job) :
      SubNatRel (@S.job_costs_shifted Task oR pR Job jtR jaR costR arrR tsR j j')
        (I.Prosa_Analysis_Facts_ShiftedJobCosts_job_costs_shifted
          Task dT oL pL Job dJ jtL jaL costL arrL tsL j j').
    Proof.
      unfold S.job_costs_shifted.
      cbn [I.Prosa_Analysis_Facts_ShiftedJobCosts_job_costs_shifted].
      apply sjc_cond_related.
      - apply ar_bool_and_related.
        + exact (ar_decide_le_related _ _ _ _ OMAX (Hja j)).
        + apply ar_bool_and_related.
          * exact (ar_decide_le_related _ _ _ _ (sub_add_correspondence _ _ _ _ OMAX HP) (Hja j')).
          * exact (ar_decide_lt_related _ _ _ _ (Hja j')
              (sub_add_correspondence _ _ _ _ OMAX
                (lcmseqdm_mul_correspondence _ _ _ _ (sub_nat_rel_canonical 2) HP))).
      - rewrite -(imported_eq_to_coq_eq _ _ (Hjt j')).
        rewrite (imported_eq_to_coq_eq _ _ (corresponding_job_in_hyperperiod_correspondence Task Job oR oL Hoff
          pR pL Hp jtR jtL Hjt jaR jaL Hja arrR arrL Harr tsR tsL Hts j' _ _
          (@prosa.model.task.concept.job_task Job Task jtR j')
          (starting_instant_of_corresponding_hyperperiod_correspondence Task Job oR oL Hoff pR pL Hp jaR jaL Hja
            tsR tsL Hts j))).
        exact (Hcost _).
      - exact (Hcost j').
    Qed.

    Theorem job_costs_in_oi_correspondence (j j' : Job) :
      SubNatRel (@prosa.behavior.job.job_cost Job (@S.job_costs_in_oi Task oR pR Job jtR jaR costR arrR tsR j) j')
        (I.Prosa_Behavior_Job_JobCost_job_cost Job dJ
          (I.Prosa_Analysis_Facts_ShiftedJobCosts_job_costs_in_oi Task dT oL pL Job dJ jtL jaL costL arrL tsL j) j').
    Proof. exact (job_costs_shifted_correspondence j j'). Qed.
  End TaskSet.

  Variable tcR : prosa.model.task.concept.TaskCost Task.
  Variable tcL : I.Prosa_Model_Task_Concept_TaskCost Task dT.
  Hypothesis Htc : forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_cost Task tcR tsk)
      (I.Prosa_Model_Task_Concept_TaskCost_task_cost Task dT tcL tsk).

  Lemma sjc_valid_job_costs_rel (cR : prosa.behavior.job.JobCost Job) (cL : I.Prosa_Behavior_Job_JobCost Job dJ) :
    (forall j : Job, SubNatRel (@prosa.behavior.job.job_cost Job cR j) (I.Prosa_Behavior_Job_JobCost_job_cost Job dJ cL j)) ->
    PropSPropRel (@prosa.model.task.concept.arrivals_have_valid_job_costs Task tcR Job jtR cR arrR)
      (I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task dT tcL Job dJ jtL cL arrL).
  Proof.
    intro Hc.
    unfold prosa.model.task.concept.arrivals_have_valid_job_costs, prosa.model.task.concept.valid_job_cost.
    cbn [I.Prosa_Model_Task_Concept_arrivals_have_valid_job_costs I.Prosa_Model_Task_Concept_valid_job_cost].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    rewrite (imported_eq_to_coq_eq _ _ (Hjt j)).
    exact (ar_bool_truth_correspondence _ _ (ar_decide_le_related _ _ _ _ (Hc j) (Htc _))).
  Qed.

  Lemma sjc_all_jobs_from_taskset_rel tsR tsL :
    ArListRel tsR tsL ->
    PropSPropRel (@prosa.model.task.concept.all_jobs_from_taskset Task Job jtR arrR tsR)
      (I.Prosa_Model_Task_Concept_all_jobs_from_taskset Task dT Job dJ jtL arrL tsL).
  Proof.
    intro Hts.
    unfold prosa.model.task.concept.all_jobs_from_taskset.
    cbn [I.Prosa_Model_Task_Concept_all_jobs_from_taskset].
    apply ar_forall_identity_correspondence => j.
    apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
    rewrite (imported_eq_to_coq_eq _ _ (Hjt j)).
    exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task _ _ _ Hts)).
  Qed.

  Definition src_job_costs_shifted_valid : Prop :=
    ltac:(body_of (fun s : S.statement_job_costs_shifted_valid => s Task oR pR tcR Job jtR jaR costR arrR)).
  Definition tgt_job_costs_shifted_valid : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_ShiftedJobCosts_job_costs_shifted_valid
      Task dT oL pL Job dJ jtL jaL costL tcL arrL)).
  Theorem job_costs_shifted_valid_correspondence :
    PropSPropRel src_job_costs_shifted_valid tgt_job_costs_shifted_valid.
  Proof.
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply ar_imp_correspondence; [exact (sjc_valid_job_costs_rel costR costL Hcost)|].
    apply sjc_forall_list_correspondence. intros tsR tsL Hts.
    apply ar_imp_correspondence;
      [exact (taskset_respects_periodic_task_model_correspondence Task pR pL Hp tsR tsL Hts Job jtR jtL Hjt
        jaR jaL Hja arrR arrL Harr)|].
    apply ar_imp_correspondence; [exact (valid_periods_correspondence Task pR pL Hp tsR tsL Hts)|].
    apply ar_imp_correspondence;
      [exact (valid_offsets_correspondence Task oR oL Hoff Job jtR jtL Hjt jaR jaL Hja arrR arrL Harr tsR tsL Hts)|].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_imp_correspondence; [exact (infinite_jobs_correspondence Task Job jtR jtL Hjt jaR jaL Hja arrR arrL Harr)|].
    apply ar_imp_correspondence; [exact (sjc_all_jobs_from_taskset_rel tsR tsL Hts)|].
    exact (sjc_valid_job_costs_rel _ _ (job_costs_in_oi_correspondence tsR tsL Hts j)).
  Qed.
End ShiftedJobCosts.
