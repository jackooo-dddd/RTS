From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import model.task.concept.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTaskCost ImportedSubadditivity.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  TaskCostBaseAdapter.

(** The three class parameters of this source file are related inputs.
    These record-level witnesses cover the observable fields in both
    directions, using the accepted Nat relation and the local eqType adapter. *)

Definition TcJobTaskRel (Job Task : eqType)
    (jobTaskR : prosa.model.task.concept.JobTask Job Task)
    (jobTaskL : ImportedTaskCost.Prosa_Model_Task_Concept_JobTask
      Job (tc_decidable_eq Job) Task (tc_decidable_eq Task)) : SProp :=
  forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jobTaskR j)
      (ImportedTaskCost.Prosa_Model_Task_Concept_JobTask_job_task
        Job (tc_decidable_eq Job) Task (tc_decidable_eq Task) jobTaskL j).

Definition tc_import_job_task (Job Task : eqType)
    (jobTaskR : prosa.model.task.concept.JobTask Job Task) :
    ImportedTaskCost.Prosa_Model_Task_Concept_JobTask
      Job (tc_decidable_eq Job) Task (tc_decidable_eq Task) :=
  ImportedTaskCost.Prosa_Model_Task_Concept_JobTask_mk
    Job (tc_decidable_eq Job) Task (tc_decidable_eq Task)
    (fun j => @prosa.model.task.concept.job_task Job Task jobTaskR j).

Definition tc_export_job_task (Job Task : eqType)
    (jobTaskL : ImportedTaskCost.Prosa_Model_Task_Concept_JobTask
      Job (tc_decidable_eq Job) Task (tc_decidable_eq Task)) :
    prosa.model.task.concept.JobTask Job Task :=
  fun j => ImportedTaskCost.Prosa_Model_Task_Concept_JobTask_job_task
    Job (tc_decidable_eq Job) Task (tc_decidable_eq Task) jobTaskL j.

Lemma tc_job_task_import_certificate (Job Task : eqType)
    (jobTaskR : prosa.model.task.concept.JobTask Job Task) :
  TcJobTaskRel Job Task jobTaskR (tc_import_job_task Job Task jobTaskR).
Proof. intro j. exact (@Lean.eq_refl _ _). Qed.

Lemma tc_job_task_export_certificate (Job Task : eqType)
    (jobTaskL : ImportedTaskCost.Prosa_Model_Task_Concept_JobTask
      Job (tc_decidable_eq Job) Task (tc_decidable_eq Task)) :
  TcJobTaskRel Job Task (tc_export_job_task Job Task jobTaskL) jobTaskL.
Proof. intro j. exact (@Lean.eq_refl _ _). Qed.

Definition TcTaskCostRel (Task : eqType)
    (costR : prosa.model.task.concept.TaskCost Task)
    (costL : ImportedTaskCost.Prosa_Model_Task_Concept_TaskCost
      Task (tc_decidable_eq Task)) : SProp :=
  forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_cost Task costR tsk)
      (ImportedTaskCost.Prosa_Model_Task_Concept_TaskCost_task_cost
        Task (tc_decidable_eq Task) costL tsk).

Definition tc_import_task_cost (Task : eqType)
    (costR : prosa.model.task.concept.TaskCost Task) :
    ImportedTaskCost.Prosa_Model_Task_Concept_TaskCost
      Task (tc_decidable_eq Task) :=
  ImportedTaskCost.Prosa_Model_Task_Concept_TaskCost_mk
    Task (tc_decidable_eq Task)
    (fun tsk => sub_nat_to_imported
      (@prosa.model.task.concept.task_cost Task costR tsk)).

Definition tc_export_task_cost (Task : eqType)
    (costL : ImportedTaskCost.Prosa_Model_Task_Concept_TaskCost
      Task (tc_decidable_eq Task)) :
    prosa.model.task.concept.TaskCost Task :=
  fun tsk => sub_nat_to_rocq
    (ImportedTaskCost.Prosa_Model_Task_Concept_TaskCost_task_cost
      Task (tc_decidable_eq Task) costL tsk).

Lemma tc_task_cost_import_certificate (Task : eqType)
    (costR : prosa.model.task.concept.TaskCost Task) :
  TcTaskCostRel Task costR (tc_import_task_cost Task costR).
Proof. intro tsk. exact (sub_nat_rel_canonical _). Qed.

Lemma tc_task_cost_export_certificate (Task : eqType)
    (costL : ImportedTaskCost.Prosa_Model_Task_Concept_TaskCost
      Task (tc_decidable_eq Task)) :
  TcTaskCostRel Task (tc_export_task_cost Task costL) costL.
Proof. intro tsk. exact (sub_nat_rel_surjective _). Qed.

Definition TcJobCostRel (Job : eqType)
    (costR : prosa.behavior.job.JobCost Job)
    (costL : ImportedTaskCost.Prosa_Behavior_Job_JobCost
      Job (tc_decidable_eq Job)) : SProp :=
  forall j : Job,
    SubNatRel (@prosa.behavior.job.job_cost Job costR j)
      (ImportedTaskCost.Prosa_Behavior_Job_JobCost_job_cost
        Job (tc_decidable_eq Job) costL j).

Definition tc_import_job_cost (Job : eqType)
    (costR : prosa.behavior.job.JobCost Job) :
    ImportedTaskCost.Prosa_Behavior_Job_JobCost
      Job (tc_decidable_eq Job) :=
  ImportedTaskCost.Prosa_Behavior_Job_JobCost_mk
    Job (tc_decidable_eq Job)
    (fun j => sub_nat_to_imported
      (@prosa.behavior.job.job_cost Job costR j)).

Definition tc_export_job_cost (Job : eqType)
    (costL : ImportedTaskCost.Prosa_Behavior_Job_JobCost
      Job (tc_decidable_eq Job)) :
    prosa.behavior.job.JobCost Job :=
  fun j => sub_nat_to_rocq
    (ImportedTaskCost.Prosa_Behavior_Job_JobCost_job_cost
      Job (tc_decidable_eq Job) costL j).

Lemma tc_job_cost_import_certificate (Job : eqType)
    (costR : prosa.behavior.job.JobCost Job) :
  TcJobCostRel Job costR (tc_import_job_cost Job costR).
Proof. intro j. exact (sub_nat_rel_canonical _). Qed.

Lemma tc_job_cost_export_certificate (Job : eqType)
    (costL : ImportedTaskCost.Prosa_Behavior_Job_JobCost
      Job (tc_decidable_eq Job)) :
  TcJobCostRel Job (tc_export_job_cost Job costL) costL.
Proof. intro j. exact (sub_nat_rel_surjective _). Qed.

Print Assumptions tc_job_task_import_certificate.
Print Assumptions tc_task_cost_import_certificate.
Print Assumptions tc_job_cost_import_certificate.
