From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From prosa Require Import analysis.definitions.job_response_time.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedJobResponseTime ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence ServiceBaseAdapter
  ServiceNatBoolOperations ServiceIntervalOperations
  ServiceScheduleOperations ServiceJobOperations ServiceCorrespondence.

(** Compose already certified arrival, addition, completion, and Boolean
    negation relations.  No source or target theorem proof is used. *)
Section JobResponseTimeCorrespondence.

  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedJobResponseTime.Prosa_Behavior_Schedule_ProcessorState Job
      (svc_decidable_eq Job).
  Variable Rstate : SvcProcessorStateRel Job PStateR PStateL.

  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : ImportedJobResponseTime.Prosa_Behavior_Schedule_schedule Job
    (svc_decidable_eq Job) PStateL.
  Hypothesis Hsched :
    SvcScheduleRel Job PStateR PStateL Rstate schedR schedL.

  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : ImportedJobResponseTime.Prosa_Behavior_Job_JobCost Job
    (svc_decidable_eq Job).
  Hypothesis Hcost : SvcJobCostRel Job costR costL.

  Variable arrivalR : prosa.behavior.job.JobArrival Job.
  Variable arrivalL : ImportedJobResponseTime.Prosa_Behavior_Job_JobArrival Job
    (svc_decidable_eq Job).
  Hypothesis Harrival : SvcJobArrivalRel Job arrivalR arrivalL.

  Lemma job_response_time_exceeds_correspondence
      (j : Job) (xR : nat) (xL : Lean.Nat) :
    SubNatRel xR xL ->
    SvcBoolRel
      (@prosa.analysis.definitions.job_response_time.job_response_time_exceeds
        Job costR arrivalR PStateR schedR j xR)
      (ImportedJobResponseTime.Prosa_Analysis_Definitions_JobResponseTime_job_response_time_exceeds
        Job (svc_decidable_eq Job) costL arrivalL PStateL schedL j xL).
  Proof.
    intro Hx.
    unfold prosa.analysis.definitions.job_response_time.job_response_time_exceeds.
    cbn [ImportedJobResponseTime.Prosa_Analysis_Definitions_JobResponseTime_job_response_time_exceeds].
    apply svc_bool_not_related.
    exact (job_response_time_bound_correspondence Job PStateR PStateL
      Rstate schedR schedL Hsched costR costL Hcost
      arrivalR arrivalL Harrival j xR xL Hx).
  Qed.

End JobResponseTimeCorrespondence.
