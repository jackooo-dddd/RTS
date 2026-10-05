From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import model.job.properties.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedJobProperties.

Check (@prosa.model.job.properties.job_cost_positive :
  forall (Job : prosa.behavior.job.JobType)
    (cost : prosa.behavior.job.JobCost Job), Job -> bool).
Check (ImportedJobProperties.Prosa_Model_Job_Properties_job_cost_positive :
  forall (Job : ImportedJobProperties.Prosa_Behavior_Job_JobType)
    (deq : ImportedJobProperties.DecidableEq Job)
    (cost : ImportedJobProperties.Prosa_Behavior_Job_JobCost Job deq),
    Job -> ImportedJobProperties.Bool).

Check (@prosa.model.job.properties.arrivals_have_positive_job_costs :
  forall (Job : prosa.behavior.job.JobType)
    (cost : prosa.behavior.job.JobCost Job),
    prosa.behavior.arrival_sequence.arrival_sequence Job -> Prop).
Check (ImportedJobProperties.Prosa_Model_Job_Properties_arrivals_have_positive_job_costs :
  forall (Job : ImportedJobProperties.Prosa_Behavior_Job_JobType)
    (deq : ImportedJobProperties.DecidableEq Job)
    (cost : ImportedJobProperties.Prosa_Behavior_Job_JobCost Job deq),
    ImportedJobProperties.Prosa_Behavior_Arrival_sequence_arrival_sequence
      Job deq -> SProp).
