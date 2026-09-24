From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From prosa Require Import analysis.definitions.finish_time.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFinishTime ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence ServiceBaseAdapter
  ServiceNatBoolOperations ServiceJobOperations ServiceScheduleOperations
  ServiceCorrespondence FinishTimeMinBridge.

(** The actual v0.6 [ex_minn] definition is related to the compiled Lean
    [Nat.find] body through the independently checked minimum bridge. *)
Section FinishTime.

  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedFinishTime.Prosa_Behavior_Schedule_ProcessorState Job
      (svc_decidable_eq Job).
  Variable Rstate : SvcProcessorStateRel Job PStateR PStateL.

  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : ImportedFinishTime.Prosa_Behavior_Schedule_schedule Job
    (svc_decidable_eq Job) PStateL.
  Hypothesis Hsched :
    SvcScheduleRel Job PStateR PStateL Rstate schedR schedL.

  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : ImportedFinishTime.Prosa_Behavior_Job_JobCost Job
    (svc_decidable_eq Job).
  Hypothesis Hcost : SvcJobCostRel Job costR costL.

  Variable arrivalR : prosa.behavior.job.JobArrival Job.
  Variable arrivalL : ImportedFinishTime.Prosa_Behavior_Job_JobArrival Job
    (svc_decidable_eq Job).
  Hypothesis Harrival : SvcJobArrivalRel Job arrivalR arrivalL.

  Lemma finish_time_correspondence (j : Job) (RR : nat) (RL : Lean.Nat)
      (HR : @prosa.behavior.service.job_response_time_bound Job PStateR
        schedR costR arrivalR j RR)
      (HL : Lean.eq
        (ImportedFinishTime.Prosa_Behavior_Service_job_response_time_bound
          Job (svc_decidable_eq Job) PStateL schedL costL arrivalL j RL)
        ImportedFinishTime.Bool_true) :
    SubNatRel RR RL ->
    SubNatRel
      (@prosa.analysis.definitions.finish_time.finish_time Job arrivalR
        costR PStateR schedR j RR HR)
      (ImportedFinishTime.Prosa_Analysis_Definitions_FinishTime_finish_time
        Job (svc_decidable_eq Job) arrivalL costL PStateL schedL j RL HL).
  Proof.
    intro HRR.
    unfold prosa.analysis.definitions.finish_time.finish_time.
    cbn [ImportedFinishTime.Prosa_Analysis_Definitions_FinishTime_finish_time].
    eapply minimum_value_correspondence.
    intros nR nL Hn.
    apply svc_bool_truth_correspondence.
    exact (completed_by_correspondence Job PStateR PStateL Rstate
      schedR schedL Hsched costR costL Hcost j nR nL Hn).
  Qed.

  Lemma finished_at_finish_time_statement_correspondence
      (j : Job) (RR : nat) (RL : Lean.Nat)
      (HR : @prosa.behavior.service.job_response_time_bound Job PStateR
        schedR costR arrivalR j RR)
      (HL : Lean.eq
        (ImportedFinishTime.Prosa_Behavior_Service_job_response_time_bound
          Job (svc_decidable_eq Job) PStateL schedL costL arrivalL j RL)
        ImportedFinishTime.Bool_true) :
    SubNatRel RR RL ->
    PropSPropRel
      (is_true (@prosa.behavior.service.completed_by Job PStateR schedR
        costR j (@prosa.analysis.definitions.finish_time.finish_time Job
          arrivalR costR PStateR schedR j RR HR)))
      (Lean.eq
        (ImportedFinishTime.Prosa_Behavior_Service_completed_by
          Job (svc_decidable_eq Job) PStateL schedL costL j
          (ImportedFinishTime.Prosa_Analysis_Definitions_FinishTime_finish_time
            Job (svc_decidable_eq Job) arrivalL costL PStateL schedL
            j RL HL))
        ImportedFinishTime.Bool_true).
  Proof.
    intro HRR. apply svc_bool_truth_correspondence.
    exact (completed_by_correspondence Job PStateR PStateL Rstate
      schedR schedL Hsched costR costL Hcost j _ _
      (finish_time_correspondence j RR RL HR HL HRR)).
  Qed.

  Lemma completes_at_finish_time_statement_correspondence
      (j : Job) (RR : nat) (RL : Lean.Nat)
      (HR : @prosa.behavior.service.job_response_time_bound Job PStateR
        schedR costR arrivalR j RR)
      (HL : Lean.eq
        (ImportedFinishTime.Prosa_Behavior_Service_job_response_time_bound
          Job (svc_decidable_eq Job) PStateL schedL costL arrivalL j RL)
        ImportedFinishTime.Bool_true) :
    SubNatRel RR RL ->
    PropSPropRel
      (is_true (@prosa.behavior.service.completes_at Job PStateR schedR
        costR j (@prosa.analysis.definitions.finish_time.finish_time Job
          arrivalR costR PStateR schedR j RR HR)))
      (Lean.eq
        (ImportedFinishTime.Prosa_Behavior_Service_completes_at
          Job (svc_decidable_eq Job) PStateL schedL costL j
          (ImportedFinishTime.Prosa_Analysis_Definitions_FinishTime_finish_time
            Job (svc_decidable_eq Job) arrivalL costL PStateL schedL
            j RL HL))
        ImportedFinishTime.Bool_true).
  Proof.
    intro HRR. apply svc_bool_truth_correspondence.
    exact (completes_at_correspondence Job PStateR PStateL Rstate
      schedR schedL Hsched costR costL Hcost j _ _
      (finish_time_correspondence j RR RL HR HL HRR)).
  Qed.

  Lemma earliest_finish_time_statement_correspondence
      (j : Job) (RR : nat) (RL : Lean.Nat)
      (HR : @prosa.behavior.service.job_response_time_bound Job PStateR
        schedR costR arrivalR j RR)
      (HL : Lean.eq
        (ImportedFinishTime.Prosa_Behavior_Service_job_response_time_bound
          Job (svc_decidable_eq Job) PStateL schedL costL arrivalL j RL)
        ImportedFinishTime.Bool_true) :
    SubNatRel RR RL ->
    PropSPropRel
      (forall tR : nat,
        is_true (@prosa.behavior.service.completed_by Job PStateR
          schedR costR j tR) ->
        is_true ((@prosa.analysis.definitions.finish_time.finish_time
          Job arrivalR costR PStateR schedR j RR HR) <= tR)%N)
      (forall tL : Lean.Nat,
        Lean.eq
          (ImportedFinishTime.Prosa_Behavior_Service_completed_by
            Job (svc_decidable_eq Job) PStateL schedL costL j tL)
          ImportedFinishTime.Bool_true ->
        ImportedFinishTime.LE_le_inst1 Lean.Nat
          ImportedFinishTime.instLENat
          (ImportedFinishTime.Prosa_Analysis_Definitions_FinishTime_finish_time
            Job (svc_decidable_eq Job) arrivalL costL PStateL schedL
            j RL HL) tL).
  Proof.
    intro HRR.
    pose Hfinish := finish_time_correspondence j RR RL HR HL HRR.
    apply prop_sprop_rel_intro.
    - intros Hsource tL HcompL.
      pose tR := sub_nat_to_rocq tL.
      have Ht : SubNatRel tR tL := sub_nat_rel_surjective tL.
      have Hcomp := svc_bool_truth_correspondence _ _
        (completed_by_correspondence Job PStateR PStateL Rstate
          schedR schedL Hsched costR costL Hcost j tR tL Ht).
      have HcompR := sprop_to_prop _ _ Hcomp HcompL.
      exact (prop_to_sprop _ _
        (svc_target_le_related _ _ _ _ Hfinish Ht)
        (Hsource tR HcompR)).
    - intro Htarget. apply strictly_inhabits.
      intros tR HcompR.
      pose tL := sub_nat_to_imported tR.
      have Ht : SubNatRel tR tL := sub_nat_rel_canonical tR.
      have Hcomp := svc_bool_truth_correspondence _ _
        (completed_by_correspondence Job PStateR PStateL Rstate
          schedR schedL Hsched costR costL Hcost j tR tL Ht).
      have HcompL := prop_to_sprop _ _ Hcomp HcompR.
      exact (sprop_to_prop _ _
        (svc_target_le_related _ _ _ _ Hfinish Ht)
        (Htarget tL HcompL)).
  Qed.

  Lemma response_time_correspondence (j : Job)
      (RR : nat) (RL : Lean.Nat)
      (HR : @prosa.behavior.service.job_response_time_bound Job PStateR
        schedR costR arrivalR j RR)
      (HL : Lean.eq
        (ImportedFinishTime.Prosa_Behavior_Service_job_response_time_bound
          Job (svc_decidable_eq Job) PStateL schedL costL arrivalL j RL)
        ImportedFinishTime.Bool_true) :
    SubNatRel RR RL ->
    SubNatRel
      (@prosa.analysis.definitions.finish_time.response_time Job arrivalR
        costR PStateR schedR j RR HR)
      (ImportedFinishTime.Prosa_Analysis_Definitions_FinishTime_response_time
        Job (svc_decidable_eq Job) arrivalL costL PStateL schedL j RL HL).
  Proof.
    intro HRR.
    unfold prosa.analysis.definitions.finish_time.response_time.
    cbn [ImportedFinishTime.Prosa_Analysis_Definitions_FinishTime_response_time].
    exact (svc_target_sub_related _ _ _ _
      (finish_time_correspondence j RR RL HR HL HRR) (Harrival j)).
  Qed.

End FinishTime.
