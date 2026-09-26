From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import model.schedule.tdma.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTdmaProjectedFull.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  TdmaBaseAdapter.

(** Equality-preserving relation for the accepted JobTask dependency. *)
Definition TdmaJobTaskRel (Job Task : eqType)
    (jobTaskR : prosa.model.task.concept.JobTask Job Task)
    (jobTaskL : ImportedTdmaProjectedFull.Prosa_Model_Task_Concept_JobTask
      Job (ar_decidable_eq Job) Task (ar_decidable_eq Task)) : SProp :=
  forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jobTaskR j)
      (ImportedTdmaProjectedFull.Prosa_Model_Task_Concept_JobTask_job_task
        Job (ar_decidable_eq Job) Task (ar_decidable_eq Task) jobTaskL j).

Definition tdma_import_job_task (Job Task : eqType)
    (jobTaskR : prosa.model.task.concept.JobTask Job Task) :
    ImportedTdmaProjectedFull.Prosa_Model_Task_Concept_JobTask
      Job (ar_decidable_eq Job) Task (ar_decidable_eq Task) :=
  ImportedTdmaProjectedFull.Prosa_Model_Task_Concept_JobTask_mk
    Job (ar_decidable_eq Job) Task (ar_decidable_eq Task)
    (fun j => @prosa.model.task.concept.job_task Job Task jobTaskR j).

Lemma tdma_job_task_source_total (Job Task : eqType)
    (jobTaskR : prosa.model.task.concept.JobTask Job Task) :
  TdmaJobTaskRel Job Task jobTaskR
    (tdma_import_job_task Job Task jobTaskR).
Proof. intro j. exact (@Lean.eq_refl _ _). Qed.

Definition TdmaJobArrivalRel (Job : eqType)
    (arrivalR : prosa.behavior.job.JobArrival Job)
    (arrivalL : ImportedTdmaProjectedFull.Prosa_Behavior_Job_JobArrival
      Job (ar_decidable_eq Job)) : SProp :=
  forall j : Job,
    SubNatRel (@prosa.behavior.job.job_arrival Job arrivalR j)
      (ImportedTdmaProjectedFull.Prosa_Behavior_Job_JobArrival_job_arrival
        Job (ar_decidable_eq Job) arrivalL j).

Definition tdma_import_job_arrival (Job : eqType)
    (arrivalR : prosa.behavior.job.JobArrival Job) :
    ImportedTdmaProjectedFull.Prosa_Behavior_Job_JobArrival
      Job (ar_decidable_eq Job) :=
  ImportedTdmaProjectedFull.Prosa_Behavior_Job_JobArrival_mk
    Job (ar_decidable_eq Job)
    (fun j => sub_nat_to_imported
      (@prosa.behavior.job.job_arrival Job arrivalR j)).

Lemma tdma_job_arrival_source_total (Job : eqType)
    (arrivalR : prosa.behavior.job.JobArrival Job) :
  TdmaJobArrivalRel Job arrivalR
    (tdma_import_job_arrival Job arrivalR).
Proof. intro j. exact (sub_nat_rel_canonical _). Qed.

Print Assumptions tdma_job_task_source_total.
Print Assumptions tdma_job_arrival_source_total.
