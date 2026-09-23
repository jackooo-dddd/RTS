From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From prosa Require Import analysis.definitions.finish_time.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFinishTime.
From FoundationCertificates Require Import ServiceBaseAdapter.

(** These guards deliberately mention the source and imported theorem
    constants.  The semantic correspondence certificate does not import this
    file and does not use either theorem proof. *)
Section Guards.
  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedFinishTime.Prosa_Behavior_Schedule_ProcessorState Job
      (svc_decidable_eq Job).
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : ImportedFinishTime.Prosa_Behavior_Schedule_schedule Job
    (svc_decidable_eq Job) PStateL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : ImportedFinishTime.Prosa_Behavior_Job_JobCost Job
    (svc_decidable_eq Job).
  Variable arrivalR : prosa.behavior.job.JobArrival Job.
  Variable arrivalL : ImportedFinishTime.Prosa_Behavior_Job_JobArrival Job
    (svc_decidable_eq Job).
  Variable j : Job.
  Variable RR : nat.
  Variable RL : Lean.Nat.
  Variable HR : @prosa.behavior.service.job_response_time_bound Job PStateR
    schedR costR arrivalR j RR.
  Variable HL : Lean.eq
    (ImportedFinishTime.Prosa_Behavior_Service_job_response_time_bound
      Job (svc_decidable_eq Job) PStateL schedL costL arrivalL j RL)
    ImportedFinishTime.Bool_true.

  Check (@prosa.analysis.definitions.finish_time.finished_at_finish_time
    Job arrivalR costR PStateR schedR j RR HR :
    is_true (@prosa.behavior.service.completed_by Job PStateR schedR costR j
      (@prosa.analysis.definitions.finish_time.finish_time Job arrivalR
        costR PStateR schedR j RR HR))).
  Check (ImportedFinishTime.Prosa_Analysis_Definitions_FinishTime_finished_at_finish_time
    Job (svc_decidable_eq Job) arrivalL costL PStateL schedL j RL HL :
    Lean.eq (ImportedFinishTime.Prosa_Behavior_Service_completed_by
      Job (svc_decidable_eq Job) PStateL schedL costL j
      (ImportedFinishTime.Prosa_Analysis_Definitions_FinishTime_finish_time
        Job (svc_decidable_eq Job) arrivalL costL PStateL schedL j RL HL))
      ImportedFinishTime.Bool_true).

  Check (@prosa.analysis.definitions.finish_time.earliest_finish_time
    Job arrivalR costR PStateR schedR j RR HR :
    forall tR : nat,
      is_true (@prosa.behavior.service.completed_by Job PStateR
        schedR costR j tR) ->
      is_true ((@prosa.analysis.definitions.finish_time.finish_time Job
        arrivalR costR PStateR schedR j RR HR) <= tR)%N).
  Check (ImportedFinishTime.Prosa_Analysis_Definitions_FinishTime_earliest_finish_time
    Job (svc_decidable_eq Job) arrivalL costL PStateL schedL j RL HL :
    forall tL : Lean.Nat,
      Lean.eq (ImportedFinishTime.Prosa_Behavior_Service_completed_by
        Job (svc_decidable_eq Job) PStateL schedL costL j tL)
        ImportedFinishTime.Bool_true ->
      ImportedFinishTime.LE_le_inst1 Lean.Nat ImportedFinishTime.instLENat
        (ImportedFinishTime.Prosa_Analysis_Definitions_FinishTime_finish_time
          Job (svc_decidable_eq Job) arrivalL costL PStateL schedL j RL HL)
        tL).

  Check (@prosa.analysis.definitions.finish_time.completes_at_finish_time
    Job arrivalR costR PStateR schedR j RR HR :
    is_true (@prosa.behavior.service.completes_at Job PStateR schedR costR j
      (@prosa.analysis.definitions.finish_time.finish_time Job arrivalR
        costR PStateR schedR j RR HR))).
  Check (ImportedFinishTime.Prosa_Analysis_Definitions_FinishTime_completes_at_finish_time
    Job (svc_decidable_eq Job) arrivalL costL PStateL schedL j RL HL :
    Lean.eq (ImportedFinishTime.Prosa_Behavior_Service_completes_at
      Job (svc_decidable_eq Job) PStateL schedL costL j
      (ImportedFinishTime.Prosa_Analysis_Definitions_FinishTime_finish_time
        Job (svc_decidable_eq Job) arrivalL costL PStateL schedL j RL HL))
      ImportedFinishTime.Bool_true).
End Guards.
