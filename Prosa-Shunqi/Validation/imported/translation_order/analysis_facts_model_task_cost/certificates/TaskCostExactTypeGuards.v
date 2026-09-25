From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTaskCost.

(** Independently stated exact imported theorem interfaces.  These guards may
    name the theorem constants; the semantic correspondences may not. *)

Definition tc_positive_target_type_guard
    (Task : ImportedTaskCost.Prosa_Model_Task_Concept_TaskType)
    (taskEq : ImportedTaskCost.DecidableEq Task)
    (Job : ImportedTaskCost.Prosa_Behavior_Job_JobType)
    (jobEq : ImportedTaskCost.DecidableEq Job)
    (jobTask : ImportedTaskCost.Prosa_Model_Task_Concept_JobTask
      Job jobEq Task taskEq)
    (jobCost : ImportedTaskCost.Prosa_Behavior_Job_JobCost Job jobEq)
    (taskCost : ImportedTaskCost.Prosa_Model_Task_Concept_TaskCost
      Task taskEq)
    (tsk : Task) (j : Job) :
    Lean.eq
      (ImportedTaskCost.Prosa_Model_Task_Concept_job_of_task
        Job jobEq Task taskEq jobTask tsk j)
      ImportedTaskCost.Bool_true ->
    Lean.eq
      (ImportedTaskCost.Prosa_Model_Job_Properties_job_cost_positive
        Job jobEq jobCost j)
      ImportedTaskCost.Bool_true ->
    Lean.eq
      (ImportedTaskCost.Prosa_Model_Task_Concept_valid_job_cost
        Task taskEq taskCost Job jobEq jobTask jobCost j)
      ImportedTaskCost.Bool_true ->
    ImportedTaskCost.LT_lt_inst1 Lean.Nat ImportedTaskCost.instLTNat
      Lean.Nat_zero
      (ImportedTaskCost.Prosa_Model_Task_Concept_TaskCost_task_cost
        Task taskEq taskCost tsk) :=
  ImportedTaskCost.Prosa_Analysis_Facts_Model_TaskCost_job_cost_positive_implies_task_cost_positive
    Task taskEq Job jobEq jobTask jobCost taskCost tsk j.

Definition tc_sum_target_type_guard
    (Task : ImportedTaskCost.Prosa_Model_Task_Concept_TaskType)
    (taskEq : ImportedTaskCost.DecidableEq Task)
    (taskCost : ImportedTaskCost.Prosa_Model_Task_Concept_TaskCost
      Task taskEq)
    (Job : ImportedTaskCost.Prosa_Behavior_Job_JobType)
    (jobEq : ImportedTaskCost.DecidableEq Job)
    (jobCost : ImportedTaskCost.Prosa_Behavior_Job_JobCost Job jobEq)
    (jobTask : ImportedTaskCost.Prosa_Model_Task_Concept_JobTask
      Job jobEq Task taskEq)
    (tsk : Task) (js : ImportedTaskCost.List Job) :
    (forall j : Job,
      ImportedTaskCost.Membership_mem Job
        (ImportedTaskCost.List Job)
        (ImportedTaskCost.List_instMembership Job) js j ->
      Lean.eq
        (ImportedTaskCost.Bool_and
          (ImportedTaskCost.Prosa_Model_Task_Concept_job_of_task
            Job jobEq Task taskEq jobTask tsk j)
          (ImportedTaskCost.Prosa_Model_Task_Concept_valid_job_cost
            Task taskEq taskCost Job jobEq jobTask jobCost j))
        ImportedTaskCost.Bool_true) ->
    ImportedTaskCost.LE_le_inst1 Lean.Nat ImportedTaskCost.instLENat
      (ImportedTaskCost.List_sum_inst1 Lean.Nat
        ImportedTaskCost.instAddNat
        (ImportedTaskCost.MulZeroClass_toZero_inst1 Lean.Nat
          ImportedTaskCost.Nat_instMulZeroClass)
        (ImportedTaskCost.List_map_inst2 Job Lean.Nat
          (ImportedTaskCost.Prosa_Behavior_Job_JobCost_job_cost
            Job jobEq jobCost) js))
      (ImportedTaskCost.HMul_hMul_inst7 Lean.Nat Lean.Nat Lean.Nat
        (ImportedTaskCost.instHMul_inst1 Lean.Nat
          ImportedTaskCost.instMulNat)
        (ImportedTaskCost.Prosa_Model_Task_Concept_TaskCost_task_cost
          Task taskEq taskCost tsk)
        (ImportedTaskCost.List_length Job js)) :=
  ImportedTaskCost.Prosa_Analysis_Facts_Model_TaskCost_sum_job_costs_bounded
    Task taskEq taskCost Job jobEq jobCost jobTask tsk js.

Set Printing Implicit.
Check ImportedTaskCost.Prosa_Analysis_Facts_Model_TaskCost_job_cost_positive_implies_task_cost_positive.
Check ImportedTaskCost.Prosa_Analysis_Facts_Model_TaskCost_sum_job_costs_bounded.
Print Assumptions ImportedTaskCost.Prosa_Analysis_Facts_Model_TaskCost_job_cost_positive_implies_task_cost_positive.
Print Assumptions ImportedTaskCost.Prosa_Analysis_Facts_Model_TaskCost_sum_job_costs_bounded.
