From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import model.task.arrival.sporadic.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSporadic ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence.
From SporadicCertificates Require Import SporadicBaseAdapter SporadicOperations.

(** Observable source/target interfaces for this exact imported artifact. *)

Definition SpSporadicModelRel (Task : eqType)
    (modelR : prosa.model.task.arrival.sporadic.SporadicModel Task)
    (modelL :
      ImportedSporadic.Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
        (ar_decidable_eq Task)) : SProp :=
  forall tsk : Task,
    SubNatRel
      (@prosa.model.task.arrival.sporadic.task_min_inter_arrival_time
        Task modelR tsk)
      (ImportedSporadic.Prosa_Model_Task_Arrival_Sporadic_SporadicModel_task_min_inter_arrival_time
        Task (ar_decidable_eq Task) modelL tsk).

Definition sp_import_sporadic_model (Task : eqType)
    (modelR : prosa.model.task.arrival.sporadic.SporadicModel Task) :
    ImportedSporadic.Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
      (ar_decidable_eq Task) :=
  ImportedSporadic.Prosa_Model_Task_Arrival_Sporadic_SporadicModel_mk
    Task (ar_decidable_eq Task)
    (fun tsk => sub_nat_to_imported
      (@prosa.model.task.arrival.sporadic.task_min_inter_arrival_time
        Task modelR tsk)).

Definition sp_export_sporadic_model (Task : eqType)
    (modelL :
      ImportedSporadic.Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
        (ar_decidable_eq Task)) :
    prosa.model.task.arrival.sporadic.SporadicModel Task :=
  fun tsk => sub_nat_to_rocq
    (ImportedSporadic.Prosa_Model_Task_Arrival_Sporadic_SporadicModel_task_min_inter_arrival_time
      Task (ar_decidable_eq Task) modelL tsk).

Lemma sp_sporadic_model_import_certificate (Task : eqType)
    (modelR : prosa.model.task.arrival.sporadic.SporadicModel Task) :
  SpSporadicModelRel Task modelR
    (sp_import_sporadic_model Task modelR).
Proof. intro tsk. exact (sub_nat_rel_canonical _). Qed.

Lemma sp_sporadic_model_export_certificate (Task : eqType)
    (modelL :
      ImportedSporadic.Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
        (ar_decidable_eq Task)) :
  SpSporadicModelRel Task
    (sp_export_sporadic_model Task modelL) modelL.
Proof. intro tsk. exact (sub_nat_rel_surjective _). Qed.

Definition SpJobTaskRel (Job Task : eqType)
    (jobTaskR : prosa.model.task.concept.JobTask Job Task)
    (jobTaskL : ImportedSporadic.Prosa_Model_Task_Concept_JobTask
      Job (ar_decidable_eq Job) Task (ar_decidable_eq Task)) : SProp :=
  forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jobTaskR j)
      (ImportedSporadic.Prosa_Model_Task_Concept_JobTask_job_task
        Job (ar_decidable_eq Job) Task (ar_decidable_eq Task) jobTaskL j).

Definition sp_import_job_task (Job Task : eqType)
    (jobTaskR : prosa.model.task.concept.JobTask Job Task) :
    ImportedSporadic.Prosa_Model_Task_Concept_JobTask
      Job (ar_decidable_eq Job) Task (ar_decidable_eq Task) :=
  ImportedSporadic.Prosa_Model_Task_Concept_JobTask_mk
    Job (ar_decidable_eq Job) Task (ar_decidable_eq Task)
    (fun j => @prosa.model.task.concept.job_task Job Task jobTaskR j).

Lemma sp_job_task_import_certificate (Job Task : eqType)
    (jobTaskR : prosa.model.task.concept.JobTask Job Task) :
  SpJobTaskRel Job Task jobTaskR
    (sp_import_job_task Job Task jobTaskR).
Proof. intro j. exact (@Lean.eq_refl _ _). Qed.

Definition SpJobArrivalRel (Job : eqType)
    (arrivalR : prosa.behavior.job.JobArrival Job)
    (arrivalL : ImportedSporadic.Prosa_Behavior_Job_JobArrival
      Job (ar_decidable_eq Job)) : SProp :=
  forall j : Job,
    SubNatRel (@prosa.behavior.job.job_arrival Job arrivalR j)
      (ImportedSporadic.Prosa_Behavior_Job_JobArrival_job_arrival
        Job (ar_decidable_eq Job) arrivalL j).

Definition sp_import_job_arrival (Job : eqType)
    (arrivalR : prosa.behavior.job.JobArrival Job) :
    ImportedSporadic.Prosa_Behavior_Job_JobArrival
      Job (ar_decidable_eq Job) :=
  ImportedSporadic.Prosa_Behavior_Job_JobArrival_mk
    Job (ar_decidable_eq Job)
    (fun j => sub_nat_to_imported
      (@prosa.behavior.job.job_arrival Job arrivalR j)).

Lemma sp_job_arrival_import_certificate (Job : eqType)
    (arrivalR : prosa.behavior.job.JobArrival Job) :
  SpJobArrivalRel Job arrivalR
    (sp_import_job_arrival Job arrivalR).
Proof. intro j. exact (sub_nat_rel_canonical _). Qed.

Definition SpTaskSetRel (Task : eqType)
    (tsR : prosa.model.task.concept.TaskSet Task)
    (tsL : ImportedSporadic.Prosa_Model_Task_Concept_TaskSet Task) : SProp :=
  ArListRel tsR tsL.

Definition sp_import_task_set (Task : eqType)
    (tsR : prosa.model.task.concept.TaskSet Task) :
    ImportedSporadic.Prosa_Model_Task_Concept_TaskSet Task :=
  ar_list_to_imported tsR.

Lemma sp_task_set_import_certificate (Task : eqType)
    (tsR : prosa.model.task.concept.TaskSet Task) :
  SpTaskSetRel Task tsR (sp_import_task_set Task tsR).
Proof. exact (@Lean.eq_refl _ _). Qed.

Print Assumptions sp_sporadic_model_import_certificate.
Print Assumptions sp_sporadic_model_export_certificate.
Print Assumptions sp_job_task_import_certificate.
Print Assumptions sp_job_arrival_import_certificate.
Print Assumptions sp_task_set_import_certificate.
