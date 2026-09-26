From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import model.aggregate.workload.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedWorkload ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence.

Module I := ImportedWorkload.

(** Definition certificates for [model/aggregate/workload.v]: for related
    inputs ([job_cost] pointwise by [SubNatRel], job predicate pointwise on
    Booleans, job list, arrival sequence, JLFP policy pointwise on Booleans,
    [job_task] by [Lean.eq], instants) the eight source definitions and the
    compiled Lean definitions are related.  Filtered sums go through
    [big_filter] and the accepted [ari_sum_related]; [xpred1] through the
    accepted [ari_decide_eq_related]; [another_hep_job] replays the accepted
    [PriorityDerived] proof on this artifact's adapter. *)

Lemma wl_sum_filter_related (T : Type) (PR : T -> bool) (PL : T -> I.Bool)
    (FR : T -> nat) (FL : T -> Lean.Nat) xsR xsL :
  ArPredRel PR PL -> (forall x, SubNatRel (FR x) (FL x)) -> ArListRel xsR xsL ->
  SubNatRel (\sum_(x <- xsR | PR x) FR x) (ari_list_sum T FL (ar_target_filter PL xsL)).
Proof.
  intros HP HF Hxs. rewrite -big_filter.
  exact (ari_sum_related T FR FL _ _ HF (ar_filter_related T PR PL xsR xsL HP Hxs)).
Qed.

Lemma wl_ne_observation (T : eqType) (x y : T) :
  ArBoolRel (x != y)
    (I.Decidable_decide (I.Ne T x y) (I.instDecidableNot (Lean.eq x y) (ar_decidable_eq T x y))).
Proof.
  unfold ar_decidable_eq, ArBoolRel.
  destruct (@eqP T x y); cbn; exact (@Lean.eq_refl _ _).
Qed.

Section Workload.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_cost Job costR j)
      (I.Prosa_Behavior_Job_JobCost_job_cost Job dJ costL j).

  Theorem workload_of_jobs_correspondence PR PL (HP : ArPredRel PR PL) jobsR jobsL
      (Hjobs : ArListRel jobsR jobsL) :
    SubNatRel (@prosa.model.aggregate.workload.workload_of_jobs Job costR PR jobsR)
      (I.Prosa_Model_Aggregate_Workload_workload_of_jobs Job dJ costL PL jobsL).
  Proof.
    unfold prosa.model.aggregate.workload.workload_of_jobs.
    cbn [I.Prosa_Model_Aggregate_Workload_workload_of_jobs].
    exact (wl_sum_filter_related Job PR PL _ _ jobsR jobsL HP Hcost Hjobs).
  Qed.

  Theorem total_workload_correspondence jobsR jobsL (Hjobs : ArListRel jobsR jobsL) :
    SubNatRel (@prosa.model.aggregate.workload.total_workload Job costR jobsR)
      (I.Prosa_Model_Aggregate_Workload_total_workload Job dJ costL jobsL).
  Proof.
    unfold prosa.model.aggregate.workload.total_workload.
    cbn [I.Prosa_Model_Aggregate_Workload_total_workload].
    refine (workload_of_jobs_correspondence _ (fun _ => I.Bool_true) _ jobsR jobsL Hjobs).
    intro x. exact (@Lean.eq_refl _ _).
  Qed.

  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Let BETWEEN t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :=
    arrivals_between_correspondence_certificate Job arrR arrL Harr _ _ _ _ H1 H2.

  Theorem workload_of_job_correspondence (j : Job) t1R t1L t2R t2L :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel (@prosa.model.aggregate.workload.workload_of_job Job costR arrR j t1R t2R)
      (I.Prosa_Model_Aggregate_Workload_workload_of_job Job dJ costL arrL j t1L t2L).
  Proof.
    intros H1 H2.
    unfold prosa.model.aggregate.workload.workload_of_job.
    cbn [I.Prosa_Model_Aggregate_Workload_workload_of_job].
    exact (workload_of_jobs_correspondence _ _ (fun x => ari_decide_eq_related Job x j) _ _
      (BETWEEN _ _ _ _ H1 H2)).
  Qed.

  Theorem total_workload_between_correspondence t1R t1L t2R t2L :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel (@prosa.model.aggregate.workload.total_workload_between Job costR arrR t1R t2R)
      (I.Prosa_Model_Aggregate_Workload_total_workload_between Job dJ costL arrL t1L t2L).
  Proof.
    intros H1 H2.
    unfold prosa.model.aggregate.workload.total_workload_between.
    cbn [I.Prosa_Model_Aggregate_Workload_total_workload_between].
    exact (total_workload_correspondence _ _ (BETWEEN _ _ _ _ H1 H2)).
  Qed.

  Section Priority.
    Variable pR : prosa.model.priority.definitions.JLFP_policy Job.
    Variable pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
    Hypothesis Hp : forall x y : Job,
      ArBoolRel (@prosa.model.priority.definitions.hep_job Job pR x y)
        (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ pL x y).

    Theorem workload_of_hep_jobs_correspondence (j : Job) t1R t1L t2R t2L :
      SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      SubNatRel (@prosa.model.aggregate.workload.workload_of_hep_jobs Job costR arrR pR j t1R t2R)
        (I.Prosa_Model_Aggregate_Workload_workload_of_hep_jobs Job dJ costL arrL pL j t1L t2L).
    Proof.
      intros H1 H2.
      unfold prosa.model.aggregate.workload.workload_of_hep_jobs.
      cbn [I.Prosa_Model_Aggregate_Workload_workload_of_hep_jobs].
      exact (workload_of_jobs_correspondence _ _ (fun x => Hp x j) _ _ (BETWEEN _ _ _ _ H1 H2)).
    Qed.

    Theorem workload_of_other_hep_jobs_correspondence (j : Job) t1R t1L t2R t2L :
      SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      SubNatRel
        (@prosa.model.aggregate.workload.workload_of_other_hep_jobs Job costR arrR pR j t1R t2R)
        (I.Prosa_Model_Aggregate_Workload_workload_of_other_hep_jobs Job dJ costL arrL pL j t1L t2L).
    Proof.
      intros H1 H2.
      unfold prosa.model.aggregate.workload.workload_of_other_hep_jobs.
      cbn [I.Prosa_Model_Aggregate_Workload_workload_of_other_hep_jobs].
      refine (workload_of_jobs_correspondence _ _ _ _ _ (BETWEEN _ _ _ _ H1 H2)).
      intro x.
      unfold prosa.model.priority.definitions.another_hep_job,
        I.Prosa_Model_Priority_Definitions_another_hep_job.
      exact (ar_bool_and_related _ _ _ _ (Hp x j) (wl_ne_observation Job x j)).
    Qed.
  End Priority.

  Section Tasks.
    Context (Task : eqType).
    Let dT := ar_decidable_eq Task.
    Variable jtR : prosa.model.task.concept.JobTask Job Task.
    Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
    Hypothesis Hjt : forall j : Job,
      Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).

    Theorem task_workload_correspondence (tsk : Task) jobsR jobsL (Hjobs : ArListRel jobsR jobsL) :
      SubNatRel (@prosa.model.aggregate.workload.task_workload Task Job jtR costR tsk jobsR)
        (I.Prosa_Model_Aggregate_Workload_task_workload Task dT Job dJ jtL costL tsk jobsL).
    Proof.
      unfold prosa.model.aggregate.workload.task_workload.
      cbn [I.Prosa_Model_Aggregate_Workload_task_workload].
      exact (workload_of_jobs_correspondence _ _
        (job_of_task_related Job Task jtR jtL Hjt tsk tsk (@Lean.eq_refl _ _)) _ _ Hjobs).
    Qed.

    Theorem task_workload_between_correspondence (tsk : Task) t1R t1L t2R t2L :
      SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      SubNatRel
        (@prosa.model.aggregate.workload.task_workload_between Task Job jtR costR arrR tsk t1R t2R)
        (I.Prosa_Model_Aggregate_Workload_task_workload_between Task dT Job dJ jtL costL arrL
          tsk t1L t2L).
    Proof.
      intros H1 H2.
      unfold prosa.model.aggregate.workload.task_workload_between.
      cbn [I.Prosa_Model_Aggregate_Workload_task_workload_between].
      exact (task_workload_correspondence tsk _ _ (BETWEEN _ _ _ _ H1 H2)).
    Qed.
  End Tasks.
End Workload.
