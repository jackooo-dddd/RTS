From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import analysis.facts.model.task_cost.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTaskCost ImportedSubadditivity.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  TaskCostBaseAdapter TaskCostClasses TaskCostOperations
  TaskCostListOperations TaskCostLogicalOperations.

(** The list input relation preserves order and multiplicity.  Together with
    the three class-field relations, it covers every operation in the source
    theorem and the actual imported Lean statement. *)
Section SumCorrespondence.
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
  Variable jsR : seq Job.
  Variable jsL : ImportedTaskCost.List Job.
  Hypothesis Hjs : TcListRel jsR jsL.

  Definition tc_target_job_cost (j : Job) : Lean.Nat :=
    ImportedTaskCost.Prosa_Behavior_Job_JobCost_job_cost
      Job (tc_decidable_eq Job) jobCostL j.

  Definition tc_target_task_cost : Lean.Nat :=
    ImportedTaskCost.Prosa_Model_Task_Concept_TaskCost_task_cost
      Task (tc_decidable_eq Task) taskCostL tsk.

  Definition tc_target_mul (a b : Lean.Nat) : Lean.Nat :=
    ImportedTaskCost.HMul_hMul_inst7 Lean.Nat Lean.Nat Lean.Nat
      (ImportedTaskCost.instHMul_inst1 Lean.Nat
        ImportedTaskCost.instMulNat) a b.

  Lemma tc_valid_jobs_premise_correspondence :
    PropSPropRel
      ({in jsR, forall j,
        @prosa.model.task.concept.job_of_task
          Job Task jobTaskR tsk j &&
        @prosa.model.task.concept.valid_job_cost
          Task taskCostR Job jobTaskR jobCostR j})
      (forall j : Job,
        tc_target_mem j jsL ->
        Lean.eq
          (ImportedTaskCost.Bool_and
            (ImportedTaskCost.Prosa_Model_Task_Concept_job_of_task
              Job (tc_decidable_eq Job) Task (tc_decidable_eq Task)
              jobTaskL tsk j)
            (ImportedTaskCost.Prosa_Model_Task_Concept_valid_job_cost
              Task (tc_decidable_eq Task) taskCostL
              Job (tc_decidable_eq Job) jobTaskL jobCostL j))
          ImportedTaskCost.Bool_true).
  Proof.
    apply tc_forall_identity_correspondence. intro j.
    apply tc_imp_correspondence.
    - exact (tc_membership_correspondence Job j jsR jsL Hjs).
    - apply tc_bool_truth_correspondence.
      exact (tc_valid_job_and_related Job Task
        jobTaskR jobTaskL HjobTask
        jobCostR jobCostL HjobCost
        taskCostR taskCostL HtaskCost tsk j).
  Qed.

  Lemma tc_sum_conclusion_correspondence :
    PropSPropRel
      (is_true
        (leq (\sum_(j <- jsR) @prosa.behavior.job.job_cost Job jobCostR j)
          (muln (@prosa.model.task.concept.task_cost Task taskCostR tsk)
            (size jsR))))
      (ImportedTaskCost.LE_le_inst1 Lean.Nat
        ImportedTaskCost.instLENat
        (tc_target_list_sum
          (ImportedTaskCost.List_map_inst2 Job Lean.Nat
            tc_target_job_cost jsL))
        (tc_target_mul tc_target_task_cost
          (ImportedTaskCost.List_length Job jsL))).
  Proof.
    have Hsum := tc_big_seq_sum_related Job
      (@prosa.behavior.job.job_cost Job jobCostR)
      tc_target_job_cost jsR jsL HjobCost Hjs.
    have Hlength := tc_length_related Job jsR jsL Hjs.
    have Hmul := sub_mul_correspondence
      (@prosa.model.task.concept.task_cost Task taskCostR tsk)
      tc_target_task_cost
      (size jsR) (ImportedTaskCost.List_length Job jsL)
      (HtaskCost tsk) Hlength.
    exact (sub_nat_le_correspondence _ _ _ _ Hsum Hmul).
  Qed.

  Lemma tc_sum_statement_correspondence :
    PropSPropRel
      ({in jsR, forall j,
        @prosa.model.task.concept.job_of_task
          Job Task jobTaskR tsk j &&
        @prosa.model.task.concept.valid_job_cost
          Task taskCostR Job jobTaskR jobCostR j} ->
       is_true
         (leq (\sum_(j <- jsR) @prosa.behavior.job.job_cost Job jobCostR j)
           (muln (@prosa.model.task.concept.task_cost Task taskCostR tsk)
             (size jsR))))
      ((forall j : Job,
        tc_target_mem j jsL ->
        Lean.eq
          (ImportedTaskCost.Bool_and
            (ImportedTaskCost.Prosa_Model_Task_Concept_job_of_task
              Job (tc_decidable_eq Job) Task (tc_decidable_eq Task)
              jobTaskL tsk j)
            (ImportedTaskCost.Prosa_Model_Task_Concept_valid_job_cost
              Task (tc_decidable_eq Task) taskCostL
              Job (tc_decidable_eq Job) jobTaskL jobCostL j))
          ImportedTaskCost.Bool_true) ->
       ImportedTaskCost.LE_le_inst1 Lean.Nat ImportedTaskCost.instLENat
         (tc_target_list_sum
           (ImportedTaskCost.List_map_inst2 Job Lean.Nat
             tc_target_job_cost jsL))
         (tc_target_mul tc_target_task_cost
           (ImportedTaskCost.List_length Job jsL))).
  Proof.
    exact (tc_imp_correspondence _ _ _ _
      tc_valid_jobs_premise_correspondence
      tc_sum_conclusion_correspondence).
  Qed.
End SumCorrespondence.

Print Assumptions tc_valid_jobs_premise_correspondence.
Print Assumptions tc_sum_conclusion_correspondence.
Print Assumptions tc_sum_statement_correspondence.
