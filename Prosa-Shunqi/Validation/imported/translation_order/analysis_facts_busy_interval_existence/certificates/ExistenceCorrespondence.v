From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import ExistenceSemanticSource.
From prosa Require Import behavior.all model.processor.platform_properties model.schedule.scheduled
  model.priority.classes model.aggregate.service_of_jobs model.aggregate.workload
  model.schedule.work_conserving model.job.properties analysis.definitions.work_bearing_readiness.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedExistence ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers
  WorkloadCorrespondence PriorityInversionCorrespondence.

Module I := ImportedExistence.
Module S := ExistenceSemanticSource.ExistenceSemanticSource.
Module B := BusyIntervalClassicalSemanticSource.BusyIntervalClassicalSemanticSource.
Module PIS := PriorityInversionSemanticSource.PriorityInversionSemanticSource.

(** Statement correspondence for [analysis/facts/busy_interval/existence.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs (task and job types, job-task, arrival and cost
    classes, arrival sequence); target side: the imported Lean theorem types.
    Inputs: [job_arrival] by [ArJobArrivalRel], [job_cost] by the accepted
    [SvcJobCostRel], [job_task] by [Lean.eq], arrival sequences by
    [ArArrivalSequenceRel].  Inputs quantified inside a statement are covered
    in both directions by explicit conversions: processor models (the
    accepted [isj_cover_pstate]), schedules through the processor-model
    relation (the accepted [fpre_forall_sched]), JLFP policies (pointwise on
    Booleans, the accepted [fpre_forall_jlfp]), the readiness instance (on the
    statement's schedule pair, the accepted [fpre_forall_jr]; it is quantified
    after the schedule), instant functions (pointwise on related Nats), tasks
    and jobs (identity) and instants.

    Over related schedules, scheduled/service/completion/pendency/idleness
    are the accepted preemption-facts and processor-model operations; the
    classical busy interval, the priority inversion and its bound are related
    by replaying the accepted busy-interval and priority-inversion definition
    certificates over those operations (they use only the scheduled and
    completion observations); the service of sets of jobs by the accepted
    filtered-sum correspondence; the workload by the accepted workload
    certificate; work conservation and work-bearing readiness by unfolding.
    No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma ex_exists_identity (T : Type) (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (exists x, PR x) (I.Exists T PL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (I.Exists_intro T PL x (prop_to_sprop _ _ (H x) Hx)).
  - intros [x Hx]. apply strictly_inhabits. exists x. exact (sprop_to_prop _ _ (H x) Hx).
Qed.

(** Instant functions, related pointwise on related arguments. *)
Definition ExFunRel (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat) : SProp :=
  forall nR nL, SubNatRel nR nL -> SubNatRel (fR nR) (fL nL).

Lemma ex_forall_fun (PR : (nat -> nat) -> Prop) (PL : (Lean.Nat -> Lean.Nat) -> SProp) :
  (forall fR fL, ExFunRel fR fL -> PropSPropRel (PR fR) (PL fL)) ->
  PropSPropRel (forall f, PR f) (forall f, PL f).
Proof.
  apply (isj_forall_cover_sprop _ _ ExFunRel
    (fun fR nL => sub_nat_to_imported (fR (sub_nat_to_rocq nL)))
    (fun fL nR => sub_nat_to_rocq (fL (sub_nat_to_imported nR)))).
  - intros fR nR nL Hn. rewrite (isj_nat_input _ _ Hn). exact (sub_nat_rel_canonical _).
  - intros fL nR nL Hn. destruct Hn. exact (sub_nat_imported_roundtrip _).
Qed.

Section Existence.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.

  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.

  Lemma ex_job_cost_positive_related (j : Job) :
    ArBoolRel (@prosa.model.job.properties.job_cost_positive Job costR j)
      (I.Prosa_Model_Job_Properties_job_cost_positive Job dJ costL j).
  Proof.
    unfold prosa.model.job.properties.job_cost_positive.
    cbn [I.Prosa_Model_Job_Properties_job_cost_positive].
    exact (svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical O) (Hcost j)).
  Qed.

  Section Pair.
    Variable PR : prosa.behavior.schedule.ProcessorState Job.
    Variable PL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
    Variable X : IsjPSRel Job PR PL.

    Lemma ex_unit_service_related :
      PropSPropRel (@prosa.model.processor.platform_properties.unit_service_proc_model Job PR)
        (I.Prosa_Model_Processor_PlatformProperties_unit_service_proc_model Job dJ PL).
    Proof.
      unfold prosa.model.processor.platform_properties.unit_service_proc_model.
      cbn [I.Prosa_Model_Processor_PlatformProperties_unit_service_proc_model].
      apply ar_forall_identity_correspondence. intro j.
      apply (isj_forall_cover_sprop _ _
        (fun sR sL => Lean.eq (isj_st_to Job PR PL X sR) sL) (isj_st_to Job PR PL X)
        (isj_st_from Job PR PL X) (fun _ => @Lean.eq_refl _ _) (isj_st_rt_target Job PR PL X)).
      intros sR sL Hs.
      exact (sub_nat_le_correspondence _ _ _ _ (isj_lean_transport
        (fun sL => SubNatRel (@prosa.behavior.schedule.service_in Job PR j sR)
           (I.Prosa_Behavior_Schedule_ProcessorState_service_in Job dJ PL j sL))
        _ _ Hs (isj_srv_in_rel Job PR PL X j sR)) (sub_nat_rel_canonical 1)).
    Qed.

    Section Sched.
      Variable sR : @prosa.behavior.schedule.schedule Job PR.
      Variable sL : I.Prosa_Behavior_Schedule_schedule Job dJ PL.
      Hypothesis Hs : IsjPSchedRel Job PR PL X sR sL.

      Let Hsa := isj_psr_scheduled_at_related Job PR PL X sR sL Hs.
      Let Hse := isj_psr_service_at_related Job PR PL X sR sL Hs.
      Let COMPLETED := fpre_completed_by_related Job costR costL Hcost PR PL X sR sL Hs.

      Lemma ex_completed_dont_execute_rel :
        PropSPropRel (@prosa.behavior.ready.completed_jobs_dont_execute Job PR sR costR)
          (I.Prosa_Behavior_Ready_completed_jobs_dont_execute Job dJ PL sL costL).
      Proof.
        unfold prosa.behavior.ready.completed_jobs_dont_execute.
        cbn [I.Prosa_Behavior_Ready_completed_jobs_dont_execute].
        apply ar_forall_identity_correspondence. intro j.
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hsa j tR tL Ht))|].
        exact (sub_nat_lt_correspondence _ _ _ _
          (fpre_service_related Job PR PL X sR sL Hs j tR tL Ht) (Hcost j)).
      Qed.

      Lemma ex_service_of_jobs_related (PRp : pred Job) (PLp : Job -> I.Bool) (HP : ArPredRel PRp PLp)
          jobsR jobsL (Hjobs : ArListRel jobsR jobsL) t1R t1L t2R t2L :
        SubNatRel t1R t1L -> SubNatRel t2R t2L ->
        SubNatRel (@prosa.model.aggregate.service_of_jobs.service_of_jobs Job PR sR PRp jobsR t1R t2R)
          (I.Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job dJ PL sL PLp jobsL t1L t2L).
      Proof.
        intros Ht1 Ht2.
        unfold prosa.model.aggregate.service_of_jobs.service_of_jobs.
        cbn [I.Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs].
        exact (isj_sum_filter_related Job PRp PLp _ _ jobsR jobsL HP
          (fun j => isj_service_during_related Job PR PL sR sL Hse j t1R t2R t1L t2L Ht1 Ht2) Hjobs).
      Qed.

      Lemma ex_total_service_related jobsR jobsL (Hjobs : ArListRel jobsR jobsL) t1R t1L t2R t2L :
        SubNatRel t1R t1L -> SubNatRel t2R t2L ->
        SubNatRel (@prosa.model.aggregate.service_of_jobs.total_service_of_jobs_in Job PR sR jobsR t1R t2R)
          (I.Prosa_Model_Aggregate_ServiceOfJobs_total_service_of_jobs_in Job dJ PL sL jobsL t1L t2L).
      Proof.
        intros Ht1 Ht2.
        unfold prosa.model.aggregate.service_of_jobs.total_service_of_jobs_in.
        cbn [I.Prosa_Model_Aggregate_ServiceOfJobs_total_service_of_jobs_in].
        refine (ex_service_of_jobs_related predT (fun _ => I.Bool_true) _ jobsR jobsL Hjobs
          t1R t1L t2R t2L Ht1 Ht2).
        intro x. exact (@Lean.eq_refl _ _).
      Qed.

      Section Arr.
        Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
        Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
        Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

        Let SCHEDJOBS := isj_scheduled_jobs_at_related Job PR PL sR sL Hsa arrR arrL Harr.

        Section Policy.
          Variable pR : prosa.model.priority.definitions.JLFP_policy Job.
          Variable pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
          Hypothesis Hp : FpreJLFPRel Job pR pL.

          (** Replayed from the accepted busy-interval and priority-inversion
              definition certificates over the pair observations. *)
          Lemma ex_quiet_time_related (j : Job) (tR : nat) (tL : Lean.Nat) :
            SubNatRel tR tL ->
            PropSPropRel (@B.quiet_time Job jaR costR PR arrR sR pR j tR)
              (I.Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time
                Job dJ jaL costL PL arrL sL pL j tL).
          Proof.
            intro Ht. unfold B.quiet_time.
            cbn [I.Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time].
            apply ar_forall_identity_correspondence. intro j_hp.
            apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL
              j_hp Harr)|].
            apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hp j_hp j))|].
            apply ar_imp_correspondence;
              [exact (ar_bool_truth_correspondence _ _
                (arrived_before_correspondence_certificate Job jaR jaL j_hp Hja tR tL Ht))|].
            exact (ar_bool_truth_correspondence _ _ (COMPLETED j_hp tR tL Ht)).
          Qed.

          Lemma ex_busy_interval_prefix_related (j : Job) t1R t1L t2R t2L :
            SubNatRel t1R t1L -> SubNatRel t2R t2L ->
            PropSPropRel (@B.busy_interval_prefix Job jaR costR PR arrR sR pR j t1R t2R)
              (I.Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix
                Job dJ jaL costL PL arrL sL pL j t1L t2L).
          Proof.
            intros H1 H2. unfold B.busy_interval_prefix.
            cbn [I.Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix].
            apply ar_and_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ H1 H2)|].
            apply ar_and_correspondence; [exact (ex_quiet_time_related j _ _ H1)|].
            apply ar_and_correspondence.
            - apply ar_forall_nat_correspondence. intros tR tL Ht.
              apply ar_imp_correspondence.
              + exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
                  (ar_decide_lt_related _ _ _ _ H1 Ht) (ar_decide_lt_related _ _ _ _ Ht H2))).
              + exact (pi_not_correspondence _ _ (ex_quiet_time_related j _ _ Ht)).
            - exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
                (ar_decide_le_related _ _ _ _ H1 (Hja j)) (ar_decide_lt_related _ _ _ _ (Hja j) H2))).
          Qed.

          Lemma ex_busy_interval_related (j : Job) t1R t1L t2R t2L :
            SubNatRel t1R t1L -> SubNatRel t2R t2L ->
            PropSPropRel (@B.busy_interval Job jaR costR PR arrR sR pR j t1R t2R)
              (I.Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval
                Job dJ jaL costL PL arrL sL pL j t1L t2L).
          Proof.
            intros H1 H2. unfold B.busy_interval.
            cbn [I.Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval].
            apply ar_and_correspondence; [exact (ex_busy_interval_prefix_related j _ _ _ _ H1 H2)|].
            exact (ex_quiet_time_related j _ _ H2).
          Qed.

          Lemma ex_priority_inversion_related (j : Job) (tR : nat) (tL : Lean.Nat) :
            SubNatRel tR tL ->
            ArBoolRel (@PIS.priority_inversion Job PR arrR sR pR j tR)
              (I.Prosa_Analysis_Definitions_PriorityInversion_priority_inversion
                Job dJ PL arrL sL pL j tL).
          Proof.
            intro Ht. unfold PIS.priority_inversion.
            cbn [I.Prosa_Analysis_Definitions_PriorityInversion_priority_inversion].
            have Hl := SCHEDJOBS tR tL Ht.
            apply ar_bool_and_related.
            - exact (svc_bool_not_related _ _ (ar_decide_mem_related Job j _ _ Hl)).
            - apply pi_has_related; [|exact Hl].
              intro jlp. exact (svc_bool_not_related _ _ (Hp jlp j)).
          Qed.

          Lemma ex_cumulative_priority_inversion_related (j : Job) (t1R t2R : nat) (t1L t2L : Lean.Nat) :
            SubNatRel t1R t1L -> SubNatRel t2R t2L ->
            SubNatRel (@PIS.cumulative_priority_inversion Job PR arrR sR pR j t1R t2R)
              (I.Prosa_Analysis_Definitions_PriorityInversion_cumulative_priority_inversion
                Job dJ PL arrL sL pL j t1L t2L).
          Proof.
            intros Ht1 Ht2.
            have Hsum := svc_interval_sum_related t1R t2R t1L t2L
              (fun t => nat_of_bool (@PIS.priority_inversion Job PR arrR sR pR j t))
              (fun t => I.Bool_toNat (I.Prosa_Analysis_Definitions_PriorityInversion_priority_inversion
                Job dJ PL arrL sL pL j t))
              Ht1 Ht2
              (fun a b Hab => pi_bool_to_nat_related _ _ (ex_priority_inversion_related j a b Hab)).
            change (SubNatRel
              (@PIS.cumulative_priority_inversion Job PR arrR sR pR j t1R t2R)
              (I.Prosa_Validation_PriorityInversionInterface_cumulPriorityInversionProjection
                Job dJ PL arrL sL pL j t1L t2L)) in Hsum.
            exact Hsum.
          Qed.

          Lemma ex_pi_bounded_related (j : Job) (BR : nat -> nat) (BL : Lean.Nat -> Lean.Nat)
              (HB : ExFunRel BR BL) :
            PropSPropRel (@PIS.priority_inversion_of_job_is_bounded_by Job jaR costR PR arrR sR pR j BR)
              (I.Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_of_job_is_bounded_by
                Job dJ jaL costL PL arrL sL pL j BL).
          Proof.
            unfold PIS.priority_inversion_of_job_is_bounded_by.
            cbn [I.Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_of_job_is_bounded_by].
            apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
            apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
            apply ar_imp_correspondence; [exact (ex_busy_interval_prefix_related j _ _ _ _ Ht1 Ht2)|].
            exact (sub_nat_le_correspondence _ _ _ _
              (ex_cumulative_priority_inversion_related j _ _ _ _ Ht1 Ht2)
              (HB _ _ (svc_target_sub_related _ _ _ _ (Hja j) Ht1))).
          Qed.

          Lemma ex_service_of_hep_related jobsR jobsL (Hjobs : ArListRel jobsR jobsL) (j : Job)
              t1R t1L t2R t2L :
            SubNatRel t1R t1L -> SubNatRel t2R t2L ->
            SubNatRel
              (@prosa.model.aggregate.service_of_jobs.service_of_higher_or_equal_priority_jobs
                Job PR sR pR jobsR j t1R t2R)
              (I.Prosa_Model_Aggregate_ServiceOfJobs_service_of_higher_or_equal_priority_jobs
                Job dJ PL sL pL jobsL j t1L t2L).
          Proof.
            intros Ht1 Ht2.
            unfold prosa.model.aggregate.service_of_jobs.service_of_higher_or_equal_priority_jobs.
            cbn [I.Prosa_Model_Aggregate_ServiceOfJobs_service_of_higher_or_equal_priority_jobs].
            exact (ex_service_of_jobs_related _ _ (fun x => Hp x j) jobsR jobsL Hjobs _ _ _ _ Ht1 Ht2).
          Qed.

          Lemma ex_workload_related (j : Job) t1R t1L t2R t2L :
            SubNatRel t1R t1L -> SubNatRel t2R t2L ->
            SubNatRel (@prosa.model.aggregate.workload.workload_of_hep_jobs Job costR arrR pR j t1R t2R)
              (I.Prosa_Model_Aggregate_Workload_workload_of_hep_jobs Job dJ costL arrL pL j t1L t2L).
          Proof.
            exact (workload_of_hep_jobs_correspondence Job costR costL Hcost arrR arrL Harr pR pL Hp
              j t1R t1L t2R t2L).
          Qed.

          Section Ready.
            Variable jrR : @prosa.behavior.ready.JobReady Job PR costR jaR.
            Variable jrL : I.Prosa_Behavior_Ready_JobReady Job dJ PL costL jaL.
            Hypothesis Hjr : FpreJrAt Job jaR jaL costR costL PR PL sR sL jrR jrL.

            Lemma ex_work_conserving_related :
              PropSPropRel (@prosa.model.schedule.work_conserving.work_conserving Job jaR costR PR jrR
                arrR sR)
                (I.Prosa_Model_Schedule_WorkConserving_work_conserving Job dJ jaL costL PL jrL arrL sL).
            Proof.
              unfold prosa.model.schedule.work_conserving.work_conserving.
              cbn [I.Prosa_Model_Schedule_WorkConserving_work_conserving].
              apply ar_forall_identity_correspondence. intro j.
              apply ar_forall_nat_correspondence. intros tR tL Ht.
              apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j
                Harr)|].
              apply ar_imp_correspondence;
                [exact (ar_bool_truth_correspondence _ _
                  (fpre_backlogged_related Job jaR jaL costR costL PR PL X sR sL Hs
                    jrR jrL Hjr j tR tL Ht))|].
              apply ex_exists_identity. intro jo.
              exact (ar_bool_truth_correspondence _ _ (Hsa jo tR tL Ht)).
            Qed.

            Lemma ex_work_bearing_related :
              PropSPropRel
                (@prosa.analysis.definitions.work_bearing_readiness.work_bearing_readiness
                  Job jaR costR PR jrR arrR sR pR)
                (I.Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness
                  Job dJ jaL costL PL jrL arrL sL pL).
            Proof.
              unfold prosa.analysis.definitions.work_bearing_readiness.work_bearing_readiness.
              cbn [I.Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness].
              apply ar_forall_identity_correspondence. intro j.
              apply ar_forall_nat_correspondence. intros tR tL Ht.
              apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j
                Harr)|].
              apply ar_imp_correspondence;
                [exact (ar_bool_truth_correspondence _ _
                  (fpre_pending_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs j tR tL Ht))|].
              apply ex_exists_identity. intro jhp.
              apply ar_and_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL
                jhp Harr)|].
              apply ar_and_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hjr jhp tR tL Ht))|].
              exact (ar_bool_truth_correspondence _ _ (Hp jhp j)).
            Qed.
          End Ready.
        End Policy.
      End Arr.
    End Sched.
  End Pair.
End Existence.

(** ** Statement correspondences *)

Section Statements.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.

  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  (* Covers used by every statement.  The recurring related pieces over the
     covered inputs (schedule validity, readiness, busy-interval prefix, quiet
     times, bounds) are written out in each proof. *)
  Local Ltac imp H := apply ar_imp_correspondence; [exact H|].
  Local Ltac va := imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
  Local Ltac cover_ps := apply (isj_cover_pstate Job); intros PR PL X;
    apply (fpre_forall_sched Job PR PL X); intros sR sL Hs.
  Local Ltac cover_jlfp := apply fpre_forall_jlfp; intros pR pL Hp.

  Let add := svc_target_add_related.

  Definition src_job_completes_within_busy_interval : Prop :=
    ltac:(body_of (fun s : S.statement_job_completes_within_busy_interval => s Job jaR costR arrR)).
  Definition tgt_job_completes_within_busy_interval : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_Existence_job_completes_within_busy_interval
      Job dJ jaL costL arrL)).

  Theorem job_completes_within_busy_interval_correspondence :
    PropSPropRel src_job_completes_within_busy_interval tgt_job_completes_within_busy_interval.
  Proof.
    unfold src_job_completes_within_busy_interval, tgt_job_completes_within_busy_interval.
    cover_ps. cover_jlfp.
    apply ar_forall_identity_correspondence. intro j.
    imp (arrives_in_correspondence_certificate Job arrR arrL j Harr). imp (fpre_reflexive_rel Job pR pL Hp).
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
    apply ar_imp_correspondence; [exact (ex_busy_interval_related Job jaR jaL Hja costR costL Hcost PR
      PL X sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2)|].
    exact (ar_bool_truth_correspondence _ _
      (fpre_completed_by_related Job costR costL Hcost PR PL X sR sL Hs j _ _ Ht2)).
  Qed.

  Definition src_not_quiet_implies_exists_pending_job : Prop :=
    ltac:(body_of (fun s : S.statement_not_quiet_implies_exists_pending_job => s Job jaR costR arrR)).
  Definition tgt_not_quiet_implies_exists_pending_job : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_Existence_not_quiet_implies_exists_pending_job
      Job dJ jaL costL arrL)).

  Theorem not_quiet_implies_exists_pending_job_correspondence :
    PropSPropRel src_not_quiet_implies_exists_pending_job tgt_not_quiet_implies_exists_pending_job.
  Proof.
    unfold src_not_quiet_implies_exists_pending_job, tgt_not_quiet_implies_exists_pending_job.
    va. cover_ps. cover_jlfp.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
    imp (sub_nat_le_correspondence _ _ _ _ Ht1 Ht2).
    apply ar_imp_correspondence; [exact (ex_quiet_time_related Job jaR jaL Hja costR costL Hcost PR PL X
      sR sL Hs arrR arrL Harr pR pL Hp j _ _ Ht1)|].
    apply ar_imp_correspondence; [apply pi_not_correspondence; exact (ex_quiet_time_related Job jaR jaL
      Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp j _ _ Ht2)|].
    apply ex_exists_identity. intro j_hp.
    apply ar_and_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j_hp Harr)|].
    apply ar_and_correspondence;
      [exact (ar_bool_truth_correspondence _ _
        (arrived_between_correspondence_certificate Job jaR jaL j_hp Hja _ _ _ _ Ht1 Ht2))|].
    apply ar_and_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hp j_hp j))|].
    exact (pi_not_correspondence _ _ (ar_bool_truth_correspondence _ _
      (fpre_completed_by_related Job costR costL Hcost PR PL X sR sL Hs j_hp _ _ Ht2))).
  Qed.

  Definition src_idle_time_implies_quiet_time_at_the_next_time_instant : Prop :=
    ltac:(body_of (fun s : S.statement_idle_time_implies_quiet_time_at_the_next_time_instant =>
      s Job jaR costR arrR)).
  Definition tgt_idle_time_implies_quiet_time_at_the_next_time_instant : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_BusyInterval_Existence_idle_time_implies_quiet_time_at_the_next_time_instant
      Job dJ jaL costL arrL)).

  Theorem idle_time_implies_quiet_time_at_the_next_time_instant_correspondence :
    PropSPropRel src_idle_time_implies_quiet_time_at_the_next_time_instant
      tgt_idle_time_implies_quiet_time_at_the_next_time_instant.
  Proof.
    unfold src_idle_time_implies_quiet_time_at_the_next_time_instant,
      tgt_idle_time_implies_quiet_time_at_the_next_time_instant.
    va. cover_ps. imp (fpre_come_from_rel Job PR PL X sR sL Hs arrR arrL Harr). imp
      (fpre_must_arrive_rel Job jaR jaL Hja PR PL X sR sL Hs). cover_jlfp. (apply (fpre_forall_jr Job
      jaR jaL Hja costR costL Hcost PR PL X sR sL Hs); intros jrR jrL Hjr). imp (ex_work_bearing_related
      Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp jrR jrL Hjr).
    apply ar_forall_identity_correspondence. intro j.
    imp (ex_work_conserving_related Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr).
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    imp (ar_bool_truth_correspondence _ _ (fpre_is_idle_related Job PR PL X sR sL Hs arrR arrL Harr _ _ Ht)).
    exact (ex_quiet_time_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL
      Hp j _ _ (pp_succ_related _ _ Ht)).
  Qed.

  Definition src_pending_hp_job_exists : Prop :=
    ltac:(body_of (fun s : S.statement_pending_hp_job_exists => s Job jaR costR arrR)).
  Definition tgt_pending_hp_job_exists : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_Existence_pending_hp_job_exists
      Job dJ jaL costL arrL)).

  Theorem pending_hp_job_exists_correspondence :
    PropSPropRel src_pending_hp_job_exists tgt_pending_hp_job_exists.
  Proof.
    unfold src_pending_hp_job_exists, tgt_pending_hp_job_exists.
    va. cover_ps. imp (fpre_must_arrive_rel Job jaR jaL Hja PR PL X sR sL Hs). cover_jlfp.
    apply ar_forall_identity_correspondence. intro j.
    imp (arrives_in_correspondence_certificate Job arrR arrL j Harr). imp (ar_bool_truth_correspondence
      _ _ (ex_job_cost_positive_related Job costR costL Hcost j)). imp (fpre_reflexive_rel Job pR pL
      Hp).
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
    apply ar_imp_correspondence; [exact (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL
      Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2)|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    imp (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
      (ar_decide_le_related _ _ _ _ Ht1 Ht) (ar_decide_lt_related _ _ _ _ Ht Ht2))).
    apply ex_exists_identity. intro jhp.
    apply ar_and_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL jhp Harr)|].
    apply ar_and_correspondence;
      [exact (ar_bool_truth_correspondence _ _
        (fpre_pending_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs jhp _ _ Ht))|].
    exact (ar_bool_truth_correspondence _ _ (Hp jhp j)).
  Qed.

  Definition src_not_quiet_implies_not_idle : Prop :=
    ltac:(body_of (fun s : S.statement_not_quiet_implies_not_idle => s Job jaR costR arrR)).
  Definition tgt_not_quiet_implies_not_idle : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_Existence_not_quiet_implies_not_idle
      Job dJ jaL costL arrL)).

  Theorem not_quiet_implies_not_idle_correspondence :
    PropSPropRel src_not_quiet_implies_not_idle tgt_not_quiet_implies_not_idle.
  Proof.
    unfold src_not_quiet_implies_not_idle, tgt_not_quiet_implies_not_idle.
    va. cover_ps. imp (fpre_come_from_rel Job PR PL X sR sL Hs arrR arrL Harr). imp
      (fpre_must_arrive_rel Job jaR jaL Hja PR PL X sR sL Hs). cover_jlfp. (apply (fpre_forall_jr Job
      jaR jaL Hja costR costL Hcost PR PL X sR sL Hs); intros jrR jrL Hjr). imp (ex_work_bearing_related
      Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp jrR jrL Hjr).
    apply ar_forall_identity_correspondence. intro j.
    imp (arrives_in_correspondence_certificate Job arrR arrL j Harr). imp (ar_bool_truth_correspondence
      _ _ (ex_job_cost_positive_related Job costR costL Hcost j)). imp (ex_work_conserving_related Job
      jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr). imp (fpre_reflexive_rel Job pR
      pL Hp).
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
    apply ar_imp_correspondence; [exact (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL
      Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2)|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    imp (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
      (ar_decide_le_related _ _ _ _ Ht1 Ht) (ar_decide_lt_related _ _ _ _ Ht Ht2))).
    exact (pi_not_correspondence _ _ (ar_bool_truth_correspondence _ _
      (fpre_is_idle_related Job PR PL X sR sL Hs arrR arrL Harr _ _ Ht))).
  Qed.

  Definition src_hep_jobs_receive_no_service_before_quiet_time : Prop :=
    ltac:(body_of (fun s : S.statement_hep_jobs_receive_no_service_before_quiet_time =>
      s Job jaR costR arrR)).
  Definition tgt_hep_jobs_receive_no_service_before_quiet_time : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_BusyInterval_Existence_hep_jobs_receive_no_service_before_quiet_time
      Job dJ jaL costL arrL)).

  Theorem hep_jobs_receive_no_service_before_quiet_time_correspondence :
    PropSPropRel src_hep_jobs_receive_no_service_before_quiet_time
      tgt_hep_jobs_receive_no_service_before_quiet_time.
  Proof.
    unfold src_hep_jobs_receive_no_service_before_quiet_time,
      tgt_hep_jobs_receive_no_service_before_quiet_time.
    va. cover_ps. imp (ex_completed_dont_execute_rel Job costR costL Hcost PR PL X sR sL Hs). cover_jlfp.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_imp_correspondence; [exact (ex_quiet_time_related Job jaR jaL Hja costR costL Hcost PR PL X
      sR sL Hs arrR arrL Harr pR pL Hp j _ _ Ht1)|].
    apply ar_forall_nat_correspondence. intros dR dL Hd.
    have Hend := add _ _ _ _ Ht1 Hd.
    exact (sub_nat_eq_correspondence _ _ _ _
      (ex_service_of_hep_related Job PR PL X sR sL Hs pR pL Hp _ _
        (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ Ht1 Hend) j _ _ _ _ Ht1 Hend)
      (ex_service_of_hep_related Job PR PL X sR sL Hs pR pL Hp _ _
        (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ (sub_nat_rel_canonical
          O) Hend)
        j _ _ _ _ Ht1 Hend)).
  Qed.

  Definition src_no_idle_time_within_non_quiet_time_interval : Prop :=
    ltac:(body_of (fun s : S.statement_no_idle_time_within_non_quiet_time_interval =>
      s Job jaR costR arrR)).
  Definition tgt_no_idle_time_within_non_quiet_time_interval : SProp :=
    ltac:(type_of_term
      (@I.Prosa_Analysis_Facts_BusyInterval_Existence_no_idle_time_within_non_quiet_time_interval
      Job dJ jaL costL arrL)).

  Theorem no_idle_time_within_non_quiet_time_interval_correspondence :
    PropSPropRel src_no_idle_time_within_non_quiet_time_interval
      tgt_no_idle_time_within_non_quiet_time_interval.
  Proof.
    unfold src_no_idle_time_within_non_quiet_time_interval,
      tgt_no_idle_time_within_non_quiet_time_interval.
    va. cover_ps. imp (fpre_come_from_rel Job PR PL X sR sL Hs arrR arrL Harr). imp
      (fpre_must_arrive_rel Job jaR jaL Hja PR PL X sR sL Hs). cover_jlfp. (apply (fpre_forall_jr Job
      jaR jaL Hja costR costL Hcost PR PL X sR sL Hs); intros jrR jrL Hjr). imp (ex_work_bearing_related
      Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp jrR jrL Hjr).
    apply ar_forall_identity_correspondence. intro j.
    imp (ex_work_conserving_related Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL
      Hjr). imp (arrival_sequence_uniq_correspondence_certificate Job arrR arrL Harr).
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_forall_nat_correspondence. intros dR dL Hd.
    apply ar_imp_correspondence; [(apply ar_forall_nat_correspondence; let tR := fresh "tR" in let tL :=
      fresh "tL" in let Ht := fresh "Ht" in intros tR tL Ht; apply ar_imp_correspondence; [ exact
      (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _ (ar_decide_lt_related _ _ _ _ Ht1
      Ht) (ar_decide_le_related _ _ _ _ Ht (svc_target_add_related _ _ _ _ Ht1 Hd)))) | apply
      pi_not_correspondence; exact (ex_quiet_time_related Job jaR jaL Hja costR costL Hcost PR PL X sR
      sL Hs arrR arrL Harr pR pL Hp j _ _ Ht) ])|].
    (imp (isj_psr_uniprocessor_related Job PR PL X); imp (ex_unit_service_related Job PR PL X); imp
      (isj_psr_ideal_progress_related Job PR PL X)).
    have Hend := add _ _ _ _ Ht1 Hd.
    exact (sub_nat_eq_correspondence _ _ _ _
      (ex_total_service_related Job PR PL X sR sL Hs _ _
        (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ (sub_nat_rel_canonical
          O) Hend)
        _ _ _ _ Ht1 Hend) Hd).
  Qed.

  Definition src_exists_busy_interval_prefix : Prop :=
    ltac:(body_of (fun s : S.statement_exists_busy_interval_prefix => s Job jaR costR arrR)).
  Definition tgt_exists_busy_interval_prefix : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_Existence_exists_busy_interval_prefix
      Job dJ jaL costL arrL)).

  Theorem exists_busy_interval_prefix_correspondence :
    PropSPropRel src_exists_busy_interval_prefix tgt_exists_busy_interval_prefix.
  Proof.
    unfold src_exists_busy_interval_prefix, tgt_exists_busy_interval_prefix.
    va. cover_ps. cover_jlfp.
    apply ar_forall_identity_correspondence. intro j.
    imp (arrives_in_correspondence_certificate Job arrR arrL j Harr). imp (fpre_reflexive_rel Job pR pL Hp).
    apply ar_forall_nat_correspondence. intros tbR tbL Htb.
    imp (ar_bool_truth_correspondence _ _ (fpre_pending_related Job jaR jaL Hja costR costL Hcost PR PL
      X sR sL Hs j _ _ Htb)).
    apply ar_exists_nat_correspondence. intros t1R t1L Ht1.
    apply ar_and_correspondence; [exact (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL
      Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 (pp_succ_related _ _ Htb))|].
    exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
      (ar_decide_le_related _ _ _ _ Ht1 (Hja j)) (ar_decide_le_related _ _ _ _ (Hja j) Htb))).
  Qed.

  Definition src_busy_interval_too_much_workload : Prop :=
    ltac:(body_of (fun s : S.statement_busy_interval_too_much_workload => s Job jaR costR arrR)).
  Definition tgt_busy_interval_too_much_workload : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_Existence_busy_interval_too_much_workload
      Job dJ jaL costL arrL)).

  Theorem busy_interval_too_much_workload_correspondence :
    PropSPropRel src_busy_interval_too_much_workload tgt_busy_interval_too_much_workload.
  Proof.
    unfold src_busy_interval_too_much_workload, tgt_busy_interval_too_much_workload.
    va. cover_ps. imp (fpre_must_arrive_rel Job jaR jaL Hja PR PL X sR sL Hs). imp
      (ex_completed_dont_execute_rel Job costR costL Hcost PR PL X sR sL Hs). cover_jlfp.
    apply ar_forall_identity_correspondence. intro j.
    imp (arrival_sequence_uniq_correspondence_certificate Job arrR arrL Harr).
    apply ar_forall_nat_correspondence. intros tbR tbL Htb.
    imp (ex_unit_service_related Job PR PL X).
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_imp_correspondence; [exact (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL
      Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 (pp_succ_related _ _ Htb))|].
    apply ar_forall_nat_correspondence. intros dR dL Hd.
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) Hd).
    apply ar_imp_correspondence; [(apply ar_forall_nat_correspondence; let tR := fresh "tR" in let tL :=
      fresh "tL" in let Ht := fresh "Ht" in intros tR tL Ht; apply ar_imp_correspondence; [ exact
      (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _ (ar_decide_lt_related _ _ _ _ Ht1
      Ht) (ar_decide_le_related _ _ _ _ Ht (svc_target_add_related _ _ _ _ Ht1 Hd)))) | apply
      pi_not_correspondence; exact (ex_quiet_time_related Job jaR jaL Hja costR costL Hcost PR PL X sR
      sL Hs arrR arrL Harr pR pL Hp j _ _ Ht) ])|].
    have Hend := add _ _ _ _ Ht1 Hd.
    exact (sub_nat_lt_correspondence _ _ _ _
      (ex_service_of_hep_related Job PR PL X sR sL Hs pR pL Hp _ _
        (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ Ht1 Hend) j _ _ _ _ Ht1 Hend)
      (ex_workload_related Job costR costL Hcost arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Hend)).
  Qed.

  Section Tasks.
    Context (Task : eqType).
    Let dT := ar_decidable_eq Task.
    Variable jtR : prosa.model.task.concept.JobTask Job Task.
    Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
    Hypothesis Hjt : forall j : Job,
      Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).




    Definition src_busy_interval_has_uninterrupted_service : Prop :=
      ltac:(body_of (fun s : S.statement_busy_interval_has_uninterrupted_service =>
        s Task Job jtR jaR costR arrR)).
    Definition tgt_busy_interval_has_uninterrupted_service : SProp :=
      ltac:(type_of_term
        (@I.Prosa_Analysis_Facts_BusyInterval_Existence_busy_interval_has_uninterrupted_service
        Job dJ Task dT jtL jaL costL arrL)).

    Theorem busy_interval_has_uninterrupted_service_correspondence :
      PropSPropRel src_busy_interval_has_uninterrupted_service
        tgt_busy_interval_has_uninterrupted_service.
    Proof.
      unfold src_busy_interval_has_uninterrupted_service, tgt_busy_interval_has_uninterrupted_service.
      ((va; cover_ps; imp (fpre_come_from_rel Job PR PL X sR sL Hs arrR arrL Harr); imp
        (fpre_must_arrive_rel Job jaR jaL Hja PR PL X sR sL Hs); imp (ex_completed_dont_execute_rel Job
        costR costL Hcost PR PL X sR sL Hs); cover_jlfp; (apply (fpre_forall_jr Job jaR jaL Hja costR
        costL Hcost PR PL X sR sL Hs); intros jrR jrL Hjr); imp (ex_work_bearing_related Job jaR jaL Hja
        costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp jrR jrL Hjr); apply
        ar_forall_identity_correspondence; let tsk := fresh "tsk" in intro tsk; apply
        ar_forall_identity_correspondence; let j := fresh "j" in intro j; imp
        (arrives_in_correspondence_certificate Job arrR arrL j Harr); imp (ar_bool_truth_correspondence
        _ _ (pi_job_of_task_related Task Job jtR jtL Hjt tsk j)); imp (ar_bool_truth_correspondence _ _
        (ex_job_cost_positive_related Job costR costL Hcost j)); imp (ex_work_conserving_related Job jaR
        jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr); imp
        (arrival_sequence_uniq_correspondence_certificate Job arrR arrL Harr); imp (fpre_reflexive_rel
        Job pR pL Hp)); apply ar_forall_nat_correspondence; intros tbR tbL Htb; imp
        (ar_bool_truth_correspondence _ _ (fpre_pending_related Job jaR jaL Hja costR costL Hcost PR PL
        X sR sL Hs j _ _ Htb)); (imp (isj_psr_uniprocessor_related Job PR PL X); imp
        (ex_unit_service_related Job PR PL X); imp (isj_psr_ideal_progress_related Job PR PL X)); apply
        ar_forall_nat_correspondence; intros t1R t1L Ht1; apply ar_imp_correspondence; [exact
        (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL
        Harr pR pL Hp j _ _ _ _ Ht1 (pp_succ_related _ _ Htb))|]; apply ex_forall_fun; intros BR BL HB;
        imp (ex_pi_bounded_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR
        pL Hp j BR BL HB); apply ar_forall_nat_correspondence; intros dR dL Hd; imp
        (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) Hd); imp (sub_nat_le_correspondence
        _ _ _ _ (add _ _ _ _ (HB _ _ (svc_target_sub_related _ _ _ _ (Hja j) Ht1)) (ex_workload_related
        Job costR costL Hcost arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 (add _ _ _ _ Ht1 Hd))) Hd)).
      apply ar_imp_correspondence; [(apply ar_forall_nat_correspondence; let tR := fresh "tR" in let tL
        := fresh "tL" in let Ht := fresh "Ht" in intros tR tL Ht; apply ar_imp_correspondence; [ exact
        (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _ (ar_decide_lt_related _ _ _ _ Ht1
        Ht) (ar_decide_le_related _ _ _ _ Ht (svc_target_add_related _ _ _ _ Ht1 Hd)))) | apply
        pi_not_correspondence; exact (ex_quiet_time_related Job jaR jaL Hja costR costL Hcost PR PL X sR
        sL Hs arrR arrL Harr pR pL Hp j _ _ Ht) ])|].
      have Hend := add _ _ _ _ Ht1 Hd.
      exact (sub_nat_le_correspondence _ _ _ _ Hd
        (add _ _ _ _ (HB _ _ (svc_target_sub_related _ _ _ _ (Hja j) Ht1))
          (ex_service_of_hep_related Job PR PL X sR sL Hs pR pL Hp _ _
            (arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ Ht1 Hend)
            j _ _ _ _ Ht1 Hend))).
    Qed.

    Definition src_busy_interval_workload_larger_than_interval : Prop :=
      ltac:(body_of (fun s : S.statement_busy_interval_workload_larger_than_interval =>
        s Task Job jtR jaR costR arrR)).
    Definition tgt_busy_interval_workload_larger_than_interval : SProp :=
      ltac:(type_of_term
        (@I.Prosa_Analysis_Facts_BusyInterval_Existence_busy_interval_workload_larger_than_interval
        Job dJ Task dT jtL jaL costL arrL)).

    Theorem busy_interval_workload_larger_than_interval_correspondence :
      PropSPropRel src_busy_interval_workload_larger_than_interval
        tgt_busy_interval_workload_larger_than_interval.
    Proof.
      unfold src_busy_interval_workload_larger_than_interval,
        tgt_busy_interval_workload_larger_than_interval.
      ((va; cover_ps; imp (fpre_come_from_rel Job PR PL X sR sL Hs arrR arrL Harr); imp
        (fpre_must_arrive_rel Job jaR jaL Hja PR PL X sR sL Hs); imp (ex_completed_dont_execute_rel Job
        costR costL Hcost PR PL X sR sL Hs); cover_jlfp; (apply (fpre_forall_jr Job jaR jaL Hja costR
        costL Hcost PR PL X sR sL Hs); intros jrR jrL Hjr); imp (ex_work_bearing_related Job jaR jaL Hja
        costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp jrR jrL Hjr); apply
        ar_forall_identity_correspondence; let tsk := fresh "tsk" in intro tsk; apply
        ar_forall_identity_correspondence; let j := fresh "j" in intro j; imp
        (arrives_in_correspondence_certificate Job arrR arrL j Harr); imp (ar_bool_truth_correspondence
        _ _ (pi_job_of_task_related Task Job jtR jtL Hjt tsk j)); imp (ar_bool_truth_correspondence _ _
        (ex_job_cost_positive_related Job costR costL Hcost j)); imp (ex_work_conserving_related Job jaR
        jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr); imp
        (arrival_sequence_uniq_correspondence_certificate Job arrR arrL Harr); imp (fpre_reflexive_rel
        Job pR pL Hp)); apply ar_forall_nat_correspondence; intros tbR tbL Htb; imp
        (ar_bool_truth_correspondence _ _ (fpre_pending_related Job jaR jaL Hja costR costL Hcost PR PL
        X sR sL Hs j _ _ Htb)); (imp (isj_psr_uniprocessor_related Job PR PL X); imp
        (ex_unit_service_related Job PR PL X); imp (isj_psr_ideal_progress_related Job PR PL X)); apply
        ar_forall_nat_correspondence; intros t1R t1L Ht1; apply ar_imp_correspondence; [exact
        (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL
        Harr pR pL Hp j _ _ _ _ Ht1 (pp_succ_related _ _ Htb))|]; apply ex_forall_fun; intros BR BL HB;
        imp (ex_pi_bounded_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR
        pL Hp j BR BL HB); apply ar_forall_nat_correspondence; intros dR dL Hd; imp
        (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) Hd); imp (sub_nat_le_correspondence
        _ _ _ _ (add _ _ _ _ (HB _ _ (svc_target_sub_related _ _ _ _ (Hja j) Ht1)) (ex_workload_related
        Job costR costL Hcost arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 (add _ _ _ _ Ht1 Hd))) Hd)).
      apply ar_imp_correspondence; [(apply ar_forall_nat_correspondence; let tR := fresh "tR" in let tL
        := fresh "tL" in let Ht := fresh "Ht" in intros tR tL Ht; apply ar_imp_correspondence; [ exact
        (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _ (ar_decide_lt_related _ _ _ _ Ht1
        Ht) (ar_decide_le_related _ _ _ _ Ht (svc_target_add_related _ _ _ _ Ht1 Hd)))) | apply
        pi_not_correspondence; exact (ex_quiet_time_related Job jaR jaL Hja costR costL Hcost PR PL X sR
        sL Hs arrR arrL Harr pR pL Hp j _ _ Ht) ])|].
      exact (sub_nat_lt_correspondence _ _ _ _ Hd
        (add _ _ _ _ (HB _ _ (svc_target_sub_related _ _ _ _ (Hja j) Ht1))
          (ex_workload_related Job costR costL Hcost arrR arrL Harr pR pL Hp j _ _ _ _ Ht1
            (add _ _ _ _ Ht1 Hd)))).
    Qed.

    Definition src_busy_interval_is_bounded : Prop :=
      ltac:(body_of (fun s : S.statement_busy_interval_is_bounded => s Task Job jtR jaR costR arrR)).
    Definition tgt_busy_interval_is_bounded : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_Existence_busy_interval_is_bounded
        Job dJ Task dT jtL jaL costL arrL)).

    Theorem busy_interval_is_bounded_correspondence :
      PropSPropRel src_busy_interval_is_bounded tgt_busy_interval_is_bounded.
    Proof.
      unfold src_busy_interval_is_bounded, tgt_busy_interval_is_bounded.
      ((va; cover_ps; imp (fpre_come_from_rel Job PR PL X sR sL Hs arrR arrL Harr); imp
        (fpre_must_arrive_rel Job jaR jaL Hja PR PL X sR sL Hs); imp (ex_completed_dont_execute_rel Job
        costR costL Hcost PR PL X sR sL Hs); cover_jlfp; (apply (fpre_forall_jr Job jaR jaL Hja costR
        costL Hcost PR PL X sR sL Hs); intros jrR jrL Hjr); imp (ex_work_bearing_related Job jaR jaL Hja
        costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp jrR jrL Hjr); apply
        ar_forall_identity_correspondence; let tsk := fresh "tsk" in intro tsk; apply
        ar_forall_identity_correspondence; let j := fresh "j" in intro j; imp
        (arrives_in_correspondence_certificate Job arrR arrL j Harr); imp (ar_bool_truth_correspondence
        _ _ (pi_job_of_task_related Task Job jtR jtL Hjt tsk j)); imp (ar_bool_truth_correspondence _ _
        (ex_job_cost_positive_related Job costR costL Hcost j)); imp (ex_work_conserving_related Job jaR
        jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr); imp
        (arrival_sequence_uniq_correspondence_certificate Job arrR arrL Harr); imp (fpre_reflexive_rel
        Job pR pL Hp)); apply ar_forall_nat_correspondence; intros tbR tbL Htb; imp
        (ar_bool_truth_correspondence _ _ (fpre_pending_related Job jaR jaL Hja costR costL Hcost PR PL
        X sR sL Hs j _ _ Htb)); (imp (isj_psr_uniprocessor_related Job PR PL X); imp
        (ex_unit_service_related Job PR PL X); imp (isj_psr_ideal_progress_related Job PR PL X)); apply
        ar_forall_nat_correspondence; intros t1R t1L Ht1; apply ar_imp_correspondence; [exact
        (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL
        Harr pR pL Hp j _ _ _ _ Ht1 (pp_succ_related _ _ Htb))|]; apply ex_forall_fun; intros BR BL HB;
        imp (ex_pi_bounded_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR
        pL Hp j BR BL HB); apply ar_forall_nat_correspondence; intros dR dL Hd; imp
        (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) Hd); imp (sub_nat_le_correspondence
        _ _ _ _ (add _ _ _ _ (HB _ _ (svc_target_sub_related _ _ _ _ (Hja j) Ht1)) (ex_workload_related
        Job costR costL Hcost arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 (add _ _ _ _ Ht1 Hd))) Hd)).
      apply ar_exists_nat_correspondence. intros t2R t2L Ht2.
      apply ar_and_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Ht2 (add _ _ _ _ Ht1 Hd))|].
      exact (ex_busy_interval_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr
        pR pL Hp j _ _ _ _ Ht1 Ht2).
    Qed.

    Definition src_exists_busy_interval : Prop :=
      ltac:(body_of (fun s : S.statement_exists_busy_interval => s Task Job jtR jaR costR arrR)).
    Definition tgt_exists_busy_interval : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_Existence_exists_busy_interval
        Job dJ Task dT jtL jaL costL arrL)).

    Theorem exists_busy_interval_correspondence :
      PropSPropRel src_exists_busy_interval tgt_exists_busy_interval.
    Proof.
      unfold src_exists_busy_interval, tgt_exists_busy_interval.
      ((va; cover_ps; imp (fpre_come_from_rel Job PR PL X sR sL Hs arrR arrL Harr); imp
        (fpre_must_arrive_rel Job jaR jaL Hja PR PL X sR sL Hs); imp (ex_completed_dont_execute_rel Job
        costR costL Hcost PR PL X sR sL Hs); cover_jlfp; (apply (fpre_forall_jr Job jaR jaL Hja costR
        costL Hcost PR PL X sR sL Hs); intros jrR jrL Hjr); imp (ex_work_bearing_related Job jaR jaL Hja
        costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp jrR jrL Hjr); apply
        ar_forall_identity_correspondence; let tsk := fresh "tsk" in intro tsk; apply
        ar_forall_identity_correspondence; let j := fresh "j" in intro j; imp
        (arrives_in_correspondence_certificate Job arrR arrL j Harr); imp (ar_bool_truth_correspondence
        _ _ (pi_job_of_task_related Task Job jtR jtL Hjt tsk j)); imp (ar_bool_truth_correspondence _ _
        (ex_job_cost_positive_related Job costR costL Hcost j)); imp (ex_work_conserving_related Job jaR
        jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr); imp
        (arrival_sequence_uniq_correspondence_certificate Job arrR arrL Harr); imp (fpre_reflexive_rel
        Job pR pL Hp)); (imp (isj_psr_uniprocessor_related Job PR PL X); imp (ex_unit_service_related
        Job PR PL X); imp (isj_psr_ideal_progress_related Job PR PL X)); apply ex_forall_fun; intros BR
        BL HB; imp (ex_pi_bounded_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL
        Harr pR pL Hp j BR BL HB); apply ar_forall_nat_correspondence; intros dR dL Hd; imp
        (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) Hd); apply ar_imp_correspondence; [
        apply ar_forall_nat_correspondence; let tR := fresh "tR" in let tL := fresh "tL" in let Ht :=
        fresh "Ht" in intros tR tL Ht; exact (sub_nat_le_correspondence _ _ _ _ (add _ _ _ _ (HB _ _
        (svc_target_sub_related _ _ _ _ (Hja j) Ht)) (ex_workload_related Job costR costL Hcost arrR
        arrL Harr pR pL Hp j _ _ _ _ Ht (add _ _ _ _ Ht Hd))) Hd) | ]).
      imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (Hcost j)).
      apply ar_exists_nat_correspondence. intros t1R t1L Ht1.
      apply ar_exists_nat_correspondence. intros t2R t2L Ht2.
      apply ar_and_correspondence;
        [exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
          (ar_decide_le_related _ _ _ _ Ht1 (Hja j)) (ar_decide_lt_related _ _ _ _ (Hja j) Ht2)))|].
      apply ar_and_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Ht2 (add _ _ _ _ Ht1 Hd))|].
      exact (ex_busy_interval_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr
        pR pL Hp j _ _ _ _ Ht1 Ht2).
    Qed.

    Definition src_busy_interval_bounds_response_time : Prop :=
      ltac:(body_of (fun s : S.statement_busy_interval_bounds_response_time =>
        s Task Job jtR jaR costR arrR)).
    Definition tgt_busy_interval_bounds_response_time : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_Existence_busy_interval_bounds_response_time
        Job dJ Task dT jtL jaL costL arrL)).

    Theorem busy_interval_bounds_response_time_correspondence :
      PropSPropRel src_busy_interval_bounds_response_time tgt_busy_interval_bounds_response_time.
    Proof.
      unfold src_busy_interval_bounds_response_time, tgt_busy_interval_bounds_response_time.
      ((va; cover_ps; imp (fpre_come_from_rel Job PR PL X sR sL Hs arrR arrL Harr); imp
        (fpre_must_arrive_rel Job jaR jaL Hja PR PL X sR sL Hs); imp (ex_completed_dont_execute_rel Job
        costR costL Hcost PR PL X sR sL Hs); cover_jlfp; (apply (fpre_forall_jr Job jaR jaL Hja costR
        costL Hcost PR PL X sR sL Hs); intros jrR jrL Hjr); imp (ex_work_bearing_related Job jaR jaL Hja
        costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp jrR jrL Hjr); apply
        ar_forall_identity_correspondence; let tsk := fresh "tsk" in intro tsk; apply
        ar_forall_identity_correspondence; let j := fresh "j" in intro j; imp
        (arrives_in_correspondence_certificate Job arrR arrL j Harr); imp (ar_bool_truth_correspondence
        _ _ (pi_job_of_task_related Task Job jtR jtL Hjt tsk j)); imp (ar_bool_truth_correspondence _ _
        (ex_job_cost_positive_related Job costR costL Hcost j)); imp (ex_work_conserving_related Job jaR
        jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr); imp
        (arrival_sequence_uniq_correspondence_certificate Job arrR arrL Harr); imp (fpre_reflexive_rel
        Job pR pL Hp)); (imp (isj_psr_uniprocessor_related Job PR PL X); imp (ex_unit_service_related
        Job PR PL X); imp (isj_psr_ideal_progress_related Job PR PL X)); apply ex_forall_fun; intros BR
        BL HB; imp (ex_pi_bounded_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL
        Harr pR pL Hp j BR BL HB); apply ar_forall_nat_correspondence; intros dR dL Hd; imp
        (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) Hd); apply ar_imp_correspondence; [
        apply ar_forall_nat_correspondence; let tR := fresh "tR" in let tL := fresh "tL" in let Ht :=
        fresh "Ht" in intros tR tL Ht; exact (sub_nat_le_correspondence _ _ _ _ (add _ _ _ _ (HB _ _
        (svc_target_sub_related _ _ _ _ (Hja j) Ht)) (ex_workload_related Job costR costL Hcost arrR
        arrL Harr pR pL Hp j _ _ _ _ Ht (add _ _ _ _ Ht Hd))) Hd) | ]).
      exact (ar_bool_truth_correspondence _ _
        (fpre_completed_by_related Job costR costL Hcost PR PL X sR sL Hs j _ _ (add _ _ _ _ (Hja j) Hd))).
    Qed.
  End Tasks.
End Statements.
