From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From prosa Require Import model.schedule.work_conserving.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedWorkConserving
  ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence ReadyBaseAdapter
  ReadyNatBoolOperations ReadyScheduleOperations ReadyJobOperations
  ReadyServiceCorrespondence ReadyArrivalBaseAdapter ReadyArrivalOperations
  ReadyArrivalCorrespondence ReadyCorrespondence.

(** The two official v0.6 work-conserving declarations, related to the
    actual imported Lean bodies.  All hypotheses are ordinary representation
    relations for the common Job, schedule, arrival, cost and readiness
    inputs; no declaration-specific semantic premise is admitted. *)

Lemma wc_exists_identity_correspondence (T : Type)
    (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (exists x, PR x)
    (ImportedWorkConserving.Exists T PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [x Hx].
    exact (ImportedWorkConserving.Exists_intro T PL x
      (prop_to_sprop _ _ (HP x) Hx)).
  - intros [x Hx]. apply strictly_inhabits.
    exists x. exact (sprop_to_prop _ _ (HP x) Hx).
Qed.

Section WorkConservingCorrespondence.

  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedWorkConserving.Prosa_Behavior_Schedule_ProcessorState Job
      (svc_decidable_eq Job).
  Variable R : SvcProcessorStateRel Job PStateR PStateL.

  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : ImportedWorkConserving.Prosa_Behavior_Schedule_schedule
    Job (svc_decidable_eq Job) PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.

  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : ImportedWorkConserving.Prosa_Behavior_Job_JobCost Job
    (svc_decidable_eq Job).
  Hypothesis Hcost : SvcJobCostRel Job costR costL.

  Variable arrivalR : prosa.behavior.job.JobArrival Job.
  Variable arrivalL : ImportedWorkConserving.Prosa_Behavior_Job_JobArrival Job
    (svc_decidable_eq Job).
  Hypothesis Harrival : SvcJobArrivalRel Job arrivalR arrivalL.

  Variable readyR :
    @prosa.behavior.ready.JobReady Job PStateR costR arrivalR.
  Variable readyL : ImportedWorkConserving.Prosa_Behavior_Ready_JobReady Job
    (svc_decidable_eq Job) PStateL costL arrivalL.
  Hypothesis Hready : RdyJobReadyRel Job PStateR PStateL R
    costR costL arrivalR arrivalL readyR readyL.

  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL :
    ImportedWorkConserving.Prosa_Behavior_Arrival_sequence_arrival_sequence Job
      (ar_decidable_eq Job).
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Lemma work_conserving_correspondence :
    PropSPropRel
      (@prosa.model.schedule.work_conserving.work_conserving
        Job arrivalR costR PStateR readyR arrR schedR)
      (ImportedWorkConserving.Prosa_Model_Schedule_WorkConserving_work_conserving
        Job (svc_decidable_eq Job) arrivalL costL PStateL readyL
        arrL schedL).
  Proof.
    cbn [ImportedWorkConserving.Prosa_Model_Schedule_WorkConserving_work_conserving].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence.
    - exact (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    - apply ar_imp_correspondence.
      + apply svc_bool_truth_correspondence.
        exact (backlogged_correspondence Job PStateR PStateL R
          schedR schedL Hsched costR costL arrivalR arrivalL
          readyR readyL Hready j tR tL Ht).
      + apply wc_exists_identity_correspondence. intro jOther.
        apply svc_bool_truth_correspondence.
        exact (scheduled_at_correspondence Job PStateR PStateL R
          schedR schedL Hsched jOther tR tL Ht).
  Qed.

  Lemma jobs_backlogged_at_correspondence
      (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    ArListRel
      (@prosa.model.schedule.work_conserving.jobs_backlogged_at
        Job arrivalR costR PStateR readyR arrR schedR tR)
      (ImportedWorkConserving.Prosa_Model_Schedule_WorkConserving_jobs_backlogged_at
        Job (svc_decidable_eq Job) arrivalL costL PStateL readyL
        arrL schedL tL).
  Proof.
    intro Ht.
    cbn [ImportedWorkConserving.Prosa_Model_Schedule_WorkConserving_jobs_backlogged_at].
    apply ar_filter_related.
    - intro j. exact (backlogged_correspondence Job PStateR PStateL R
        schedR schedL Hsched costR costL arrivalR arrivalL
        readyR readyL Hready j tR tL Ht).
    - exact (arrivals_up_to_correspondence_certificate Job arrR arrL
        Harr tR tL Ht).
  Qed.

End WorkConservingCorrespondence.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN work_conserving_correspondence". exact I. Qed.
Print Assumptions work_conserving_correspondence.
Print Assumptions jobs_backlogged_at_correspondence.
Goal Logic.True.
Proof. idtac "AUDIT_END work_conserving_correspondence". exact I. Qed.
