From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import model.task.concept.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTaskConcept ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence ReadyArrivalBaseAdapter
  ConceptOperations.

(** Observable class interfaces for the actual imported one-field Lean records.
    Both carrier types use their source MathComp eqType and the artifact-local
    DecidableEq adapter.  Numeric fields use the established Nat relation. *)

Definition ct_task_type_to_imported (Task : eqType) :
    ImportedTaskConcept.Prosa_Model_Task_Concept_TaskType := Task.

Lemma task_type_correspondence (Task : eqType) :
  Lean.eq Task (ct_task_type_to_imported Task).
Proof. exact (@Lean.eq_refl _ _). Qed.

Definition CtJobTaskRel (Job Task : eqType)
    (jobTaskR : prosa.model.task.concept.JobTask Job Task)
    (jobTaskL : ImportedTaskConcept.Prosa_Model_Task_Concept_JobTask
      Job (ar_decidable_eq Job) Task (ar_decidable_eq Task)) : SProp :=
  forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jobTaskR j)
      (ImportedTaskConcept.Prosa_Model_Task_Concept_JobTask_job_task
        Job (ar_decidable_eq Job) Task (ar_decidable_eq Task) jobTaskL j).

Definition ct_import_job_task (Job Task : eqType)
    (jobTaskR : prosa.model.task.concept.JobTask Job Task) :
    ImportedTaskConcept.Prosa_Model_Task_Concept_JobTask
      Job (ar_decidable_eq Job) Task (ar_decidable_eq Task) :=
  ImportedTaskConcept.Prosa_Model_Task_Concept_JobTask_mk
    Job (ar_decidable_eq Job) Task (ar_decidable_eq Task)
    (fun j => @prosa.model.task.concept.job_task Job Task jobTaskR j).

Definition ct_export_job_task (Job Task : eqType)
    (jobTaskL : ImportedTaskConcept.Prosa_Model_Task_Concept_JobTask
      Job (ar_decidable_eq Job) Task (ar_decidable_eq Task)) :
    prosa.model.task.concept.JobTask Job Task :=
  fun j => ImportedTaskConcept.Prosa_Model_Task_Concept_JobTask_job_task
    Job (ar_decidable_eq Job) Task (ar_decidable_eq Task) jobTaskL j.

Lemma job_task_import_certificate (Job Task : eqType)
    (jobTaskR : prosa.model.task.concept.JobTask Job Task) :
  CtJobTaskRel Job Task jobTaskR (ct_import_job_task Job Task jobTaskR).
Proof. intro j. exact (@Lean.eq_refl _ _). Qed.

Lemma job_task_export_certificate (Job Task : eqType)
    (jobTaskL : ImportedTaskConcept.Prosa_Model_Task_Concept_JobTask
      Job (ar_decidable_eq Job) Task (ar_decidable_eq Task)) :
  CtJobTaskRel Job Task (ct_export_job_task Job Task jobTaskL) jobTaskL.
Proof. intro j. exact (@Lean.eq_refl _ _). Qed.

Definition CtTaskDeadlineRel (Task : eqType)
    (deadlineR : prosa.model.task.concept.TaskDeadline Task)
    (deadlineL : ImportedTaskConcept.Prosa_Model_Task_Concept_TaskDeadline
      Task (ar_decidable_eq Task)) : SProp :=
  forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_deadline Task deadlineR tsk)
      (ImportedTaskConcept.Prosa_Model_Task_Concept_TaskDeadline_task_deadline
        Task (ar_decidable_eq Task) deadlineL tsk).

Definition ct_import_task_deadline (Task : eqType)
    (deadlineR : prosa.model.task.concept.TaskDeadline Task) :
    ImportedTaskConcept.Prosa_Model_Task_Concept_TaskDeadline
      Task (ar_decidable_eq Task) :=
  ImportedTaskConcept.Prosa_Model_Task_Concept_TaskDeadline_mk
    Task (ar_decidable_eq Task)
    (fun tsk => sub_nat_to_imported
      (@prosa.model.task.concept.task_deadline Task deadlineR tsk)).

Definition ct_export_task_deadline (Task : eqType)
    (deadlineL : ImportedTaskConcept.Prosa_Model_Task_Concept_TaskDeadline
      Task (ar_decidable_eq Task)) :
    prosa.model.task.concept.TaskDeadline Task :=
  fun tsk => sub_nat_to_rocq
    (ImportedTaskConcept.Prosa_Model_Task_Concept_TaskDeadline_task_deadline
      Task (ar_decidable_eq Task) deadlineL tsk).

Lemma task_deadline_import_certificate (Task : eqType)
    (deadlineR : prosa.model.task.concept.TaskDeadline Task) :
  CtTaskDeadlineRel Task deadlineR
    (ct_import_task_deadline Task deadlineR).
Proof. intro tsk. exact (sub_nat_rel_canonical _). Qed.

Lemma task_deadline_export_certificate (Task : eqType)
    (deadlineL : ImportedTaskConcept.Prosa_Model_Task_Concept_TaskDeadline
      Task (ar_decidable_eq Task)) :
  CtTaskDeadlineRel Task (ct_export_task_deadline Task deadlineL) deadlineL.
Proof. intro tsk. exact (sub_nat_rel_surjective _). Qed.

Definition CtTaskCostRel (Task : eqType)
    (costR : prosa.model.task.concept.TaskCost Task)
    (costL : ImportedTaskConcept.Prosa_Model_Task_Concept_TaskCost
      Task (ar_decidable_eq Task)) : SProp :=
  forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_cost Task costR tsk)
      (ImportedTaskConcept.Prosa_Model_Task_Concept_TaskCost_task_cost
        Task (ar_decidable_eq Task) costL tsk).

Definition ct_import_task_cost (Task : eqType)
    (costR : prosa.model.task.concept.TaskCost Task) :
    ImportedTaskConcept.Prosa_Model_Task_Concept_TaskCost
      Task (ar_decidable_eq Task) :=
  ImportedTaskConcept.Prosa_Model_Task_Concept_TaskCost_mk
    Task (ar_decidable_eq Task)
    (fun tsk => sub_nat_to_imported
      (@prosa.model.task.concept.task_cost Task costR tsk)).

Definition ct_export_task_cost (Task : eqType)
    (costL : ImportedTaskConcept.Prosa_Model_Task_Concept_TaskCost
      Task (ar_decidable_eq Task)) :
    prosa.model.task.concept.TaskCost Task :=
  fun tsk => sub_nat_to_rocq
    (ImportedTaskConcept.Prosa_Model_Task_Concept_TaskCost_task_cost
      Task (ar_decidable_eq Task) costL tsk).

Lemma task_cost_import_certificate (Task : eqType)
    (costR : prosa.model.task.concept.TaskCost Task) :
  CtTaskCostRel Task costR (ct_import_task_cost Task costR).
Proof. intro tsk. exact (sub_nat_rel_canonical _). Qed.

Lemma task_cost_export_certificate (Task : eqType)
    (costL : ImportedTaskConcept.Prosa_Model_Task_Concept_TaskCost
      Task (ar_decidable_eq Task)) :
  CtTaskCostRel Task (ct_export_task_cost Task costL) costL.
Proof. intro tsk. exact (sub_nat_rel_surjective _). Qed.

Definition CtTaskMinCostRel (Task : eqType)
    (costR : prosa.model.task.concept.TaskMinCost Task)
    (costL : ImportedTaskConcept.Prosa_Model_Task_Concept_TaskMinCost
      Task (ar_decidable_eq Task)) : SProp :=
  forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_min_cost Task costR tsk)
      (ImportedTaskConcept.Prosa_Model_Task_Concept_TaskMinCost_task_min_cost
        Task (ar_decidable_eq Task) costL tsk).

Definition ct_import_task_min_cost (Task : eqType)
    (costR : prosa.model.task.concept.TaskMinCost Task) :
    ImportedTaskConcept.Prosa_Model_Task_Concept_TaskMinCost
      Task (ar_decidable_eq Task) :=
  ImportedTaskConcept.Prosa_Model_Task_Concept_TaskMinCost_mk
    Task (ar_decidable_eq Task)
    (fun tsk => sub_nat_to_imported
      (@prosa.model.task.concept.task_min_cost Task costR tsk)).

Definition ct_export_task_min_cost (Task : eqType)
    (costL : ImportedTaskConcept.Prosa_Model_Task_Concept_TaskMinCost
      Task (ar_decidable_eq Task)) :
    prosa.model.task.concept.TaskMinCost Task :=
  fun tsk => sub_nat_to_rocq
    (ImportedTaskConcept.Prosa_Model_Task_Concept_TaskMinCost_task_min_cost
      Task (ar_decidable_eq Task) costL tsk).

Lemma task_min_cost_import_certificate (Task : eqType)
    (costR : prosa.model.task.concept.TaskMinCost Task) :
  CtTaskMinCostRel Task costR (ct_import_task_min_cost Task costR).
Proof. intro tsk. exact (sub_nat_rel_canonical _). Qed.

Lemma task_min_cost_export_certificate (Task : eqType)
    (costL : ImportedTaskConcept.Prosa_Model_Task_Concept_TaskMinCost
      Task (ar_decidable_eq Task)) :
  CtTaskMinCostRel Task (ct_export_task_min_cost Task costL) costL.
Proof. intro tsk. exact (sub_nat_rel_surjective _). Qed.

Definition CtJobCostRel (Job : eqType)
    (costR : prosa.behavior.job.JobCost Job)
    (costL : ImportedTaskConcept.Prosa_Behavior_Job_JobCost
      Job (ar_decidable_eq Job)) : SProp :=
  forall j : Job,
    SubNatRel (@prosa.behavior.job.job_cost Job costR j)
      (ImportedTaskConcept.Prosa_Behavior_Job_JobCost_job_cost
        Job (ar_decidable_eq Job) costL j).

Definition ct_import_job_cost (Job : eqType)
    (costR : prosa.behavior.job.JobCost Job) :
    ImportedTaskConcept.Prosa_Behavior_Job_JobCost
      Job (ar_decidable_eq Job) :=
  ImportedTaskConcept.Prosa_Behavior_Job_JobCost_mk
    Job (ar_decidable_eq Job)
    (fun j => sub_nat_to_imported
      (@prosa.behavior.job.job_cost Job costR j)).

Definition ct_export_job_cost (Job : eqType)
    (costL : ImportedTaskConcept.Prosa_Behavior_Job_JobCost
      Job (ar_decidable_eq Job)) :
    prosa.behavior.job.JobCost Job :=
  fun j => sub_nat_to_rocq
    (ImportedTaskConcept.Prosa_Behavior_Job_JobCost_job_cost
      Job (ar_decidable_eq Job) costL j).

Lemma job_cost_import_certificate (Job : eqType)
    (costR : prosa.behavior.job.JobCost Job) :
  CtJobCostRel Job costR (ct_import_job_cost Job costR).
Proof. intro j. exact (sub_nat_rel_canonical _). Qed.

Lemma job_cost_export_certificate (Job : eqType)
    (costL : ImportedTaskConcept.Prosa_Behavior_Job_JobCost
      Job (ar_decidable_eq Job)) :
  CtJobCostRel Job (ct_export_job_cost Job costL) costL.
Proof. intro j. exact (sub_nat_rel_surjective _). Qed.

Definition CtTaskSetRel (Task : eqType)
    (tsR : prosa.model.task.concept.TaskSet Task)
    (tsL : ImportedTaskConcept.Prosa_Model_Task_Concept_TaskSet Task) : SProp :=
  ArListRel tsR tsL.

Definition ct_import_task_set (Task : eqType)
    (tsR : prosa.model.task.concept.TaskSet Task) :
    ImportedTaskConcept.Prosa_Model_Task_Concept_TaskSet Task :=
  ar_list_to_imported tsR.

Lemma task_set_correspondence (Task : eqType)
    (tsR : prosa.model.task.concept.TaskSet Task) :
  CtTaskSetRel Task tsR (ct_import_task_set Task tsR).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma task_set_export_certificate (Task : eqType)
    (tsL : ImportedTaskConcept.Prosa_Model_Task_Concept_TaskSet Task) :
  CtTaskSetRel Task (ar_list_to_rocq tsL) tsL.
Proof. exact (ar_list_target_roundtrip tsL). Qed.

Print Assumptions task_type_correspondence.
Print Assumptions job_task_import_certificate.
Print Assumptions job_task_export_certificate.
Print Assumptions task_deadline_import_certificate.
Print Assumptions task_deadline_export_certificate.
Print Assumptions task_cost_import_certificate.
Print Assumptions task_cost_export_certificate.
Print Assumptions task_min_cost_import_certificate.
Print Assumptions task_min_cost_export_certificate.
Print Assumptions task_set_correspondence.
Print Assumptions task_set_export_certificate.
Print Assumptions job_cost_import_certificate.
Print Assumptions job_cost_export_certificate.
