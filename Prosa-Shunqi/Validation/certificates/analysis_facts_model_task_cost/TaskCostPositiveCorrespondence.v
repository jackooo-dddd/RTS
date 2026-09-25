From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import analysis.facts.model.task_cost.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTaskCost ImportedSubadditivity.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  TaskCostBaseAdapter TaskCostClasses TaskCostOperations
  TaskCostLogicalOperations.

(** Fixed related-input instance of the full positive-cost theorem statement.
    No source or target theorem constant is used in the proof. *)
Section PositiveCorrespondence.
  Context (Job Task : eqType).
  Variable jobTaskR : prosa.model.task.concept.JobTask Job Task.
  Variable jobTaskL : ImportedTaskCost.Prosa_Model_Task_Concept_JobTask
    Job (tc_decidable_eq Job) Task (tc_decidable_eq Task).
  Hypothesis HjobTask : TcJobTaskRel Job Task jobTaskR jobTaskL.
  Variable jobCostR : prosa.behavior.job.JobCost Job.
  Variable jobCostL : ImportedTaskCost.Prosa_Behavior_Job_JobCost
    Job (tc_decidable_eq Job).
  Hypothesis HjobCost : TcJobCostRel Job jobCostR jobCostL.
  Variable taskCostR : prosa.model.task.concept.TaskCost Task.
  Variable taskCostL : ImportedTaskCost.Prosa_Model_Task_Concept_TaskCost
    Task (tc_decidable_eq Task).
  Hypothesis HtaskCost : TcTaskCostRel Task taskCostR taskCostL.
  Variable tsk : Task.
  Variable j : Job.

  Lemma tc_positive_statement_correspondence :
    PropSPropRel
      (is_true (@prosa.model.task.concept.job_of_task
         Job Task jobTaskR tsk j) ->
       is_true (@prosa.model.job.properties.job_cost_positive
         Job jobCostR j) ->
       is_true (@prosa.model.task.concept.valid_job_cost
         Task taskCostR Job jobTaskR jobCostR j) ->
       is_true (ltn O
         (@prosa.model.task.concept.task_cost Task taskCostR tsk)))
      (Lean.eq
         (ImportedTaskCost.Prosa_Model_Task_Concept_job_of_task
           Job (tc_decidable_eq Job) Task (tc_decidable_eq Task)
           jobTaskL tsk j) ImportedTaskCost.Bool_true ->
       Lean.eq
         (ImportedTaskCost.Prosa_Model_Job_Properties_job_cost_positive
           Job (tc_decidable_eq Job) jobCostL j)
         ImportedTaskCost.Bool_true ->
       Lean.eq
         (ImportedTaskCost.Prosa_Model_Task_Concept_valid_job_cost
           Task (tc_decidable_eq Task) taskCostL
           Job (tc_decidable_eq Job) jobTaskL jobCostL j)
         ImportedTaskCost.Bool_true ->
       tc_target_lt Lean.Nat_zero
         (ImportedTaskCost.Prosa_Model_Task_Concept_TaskCost_task_cost
           Task (tc_decidable_eq Task) taskCostL tsk)).
  Proof.
    apply tc_imp_correspondence.
    - apply tc_bool_truth_correspondence.
      exact (tc_job_of_task_related Job Task
        jobTaskR jobTaskL HjobTask tsk j).
    - apply tc_imp_correspondence.
      + apply tc_bool_truth_correspondence.
        exact (tc_job_cost_positive_related Job
          jobCostR jobCostL HjobCost j).
      + apply tc_imp_correspondence.
        * apply tc_bool_truth_correspondence.
          exact (tc_valid_job_cost_related Job Task
            jobTaskR jobTaskL HjobTask
            jobCostR jobCostL HjobCost
            taskCostR taskCostL HtaskCost j).
        * exact (sub_nat_lt_correspondence O Lean.Nat_zero
            (@prosa.model.task.concept.task_cost Task taskCostR tsk)
            (ImportedTaskCost.Prosa_Model_Task_Concept_TaskCost_task_cost
              Task (tc_decidable_eq Task) taskCostL tsk)
            (sub_nat_rel_canonical O) (HtaskCost tsk)).
  Qed.
End PositiveCorrespondence.

Print Assumptions tc_positive_statement_correspondence.
