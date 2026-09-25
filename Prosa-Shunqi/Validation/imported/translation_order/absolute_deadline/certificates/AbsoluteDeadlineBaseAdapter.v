From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From prosa Require Import model.task.absolute_deadline.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedAbsoluteDeadline.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence.

(** Artifact-local field adapters for the actual ImportedAbsoluteDeadline
    records.  Nat values and addition reuse the accepted SubNat relation. *)

Definition ad_false_to_target (H : Logic.False) :
    ImportedAbsoluteDeadline.False :=
  match H return ImportedAbsoluteDeadline.False with end.

Definition ad_decidable_eq (T : eqType) :
    ImportedAbsoluteDeadline.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H =>
        ImportedAbsoluteDeadline.Decidable_isTrue (Lean.eq x y)
          (coq_eq_to_imported_eq x y H)
    | ReflectF H =>
        ImportedAbsoluteDeadline.Decidable_isFalse (Lean.eq x y)
          (fun HL => ad_false_to_target
            (H (imported_eq_to_coq_eq x y HL)))
    end.

Definition AdJobTaskRel (Job Task : eqType)
    (jobTaskR : prosa.model.task.concept.JobTask Job Task)
    (jobTaskL : ImportedAbsoluteDeadline.Prosa_Model_Task_Concept_JobTask
      Job (ad_decidable_eq Job) Task (ad_decidable_eq Task)) : SProp :=
  forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jobTaskR j)
      (ImportedAbsoluteDeadline.Prosa_Model_Task_Concept_JobTask_job_task
        Job (ad_decidable_eq Job) Task (ad_decidable_eq Task) jobTaskL j).

Definition ad_import_job_task (Job Task : eqType)
    (jobTaskR : prosa.model.task.concept.JobTask Job Task) :
    ImportedAbsoluteDeadline.Prosa_Model_Task_Concept_JobTask
      Job (ad_decidable_eq Job) Task (ad_decidable_eq Task) :=
  ImportedAbsoluteDeadline.Prosa_Model_Task_Concept_JobTask_mk
    Job (ad_decidable_eq Job) Task (ad_decidable_eq Task)
    (fun j => @prosa.model.task.concept.job_task Job Task jobTaskR j).

Definition ad_export_job_task (Job Task : eqType)
    (jobTaskL : ImportedAbsoluteDeadline.Prosa_Model_Task_Concept_JobTask
      Job (ad_decidable_eq Job) Task (ad_decidable_eq Task)) :
    prosa.model.task.concept.JobTask Job Task :=
  fun j => ImportedAbsoluteDeadline.Prosa_Model_Task_Concept_JobTask_job_task
    Job (ad_decidable_eq Job) Task (ad_decidable_eq Task) jobTaskL j.

Lemma ad_job_task_import_certificate (Job Task : eqType)
    (jobTaskR : prosa.model.task.concept.JobTask Job Task) :
  AdJobTaskRel Job Task jobTaskR
    (ad_import_job_task Job Task jobTaskR).
Proof. intro j. exact (@Lean.eq_refl _ _). Qed.

Lemma ad_job_task_export_certificate (Job Task : eqType)
    (jobTaskL : ImportedAbsoluteDeadline.Prosa_Model_Task_Concept_JobTask
      Job (ad_decidable_eq Job) Task (ad_decidable_eq Task)) :
  AdJobTaskRel Job Task
    (ad_export_job_task Job Task jobTaskL) jobTaskL.
Proof. intro j. exact (@Lean.eq_refl _ _). Qed.

Definition AdTaskDeadlineRel (Task : eqType)
    (deadlineR : prosa.model.task.concept.TaskDeadline Task)
    (deadlineL : ImportedAbsoluteDeadline.Prosa_Model_Task_Concept_TaskDeadline
      Task (ad_decidable_eq Task)) : SProp :=
  forall tsk : Task,
    SubNatRel (@prosa.model.task.concept.task_deadline Task deadlineR tsk)
      (ImportedAbsoluteDeadline.Prosa_Model_Task_Concept_TaskDeadline_task_deadline
        Task (ad_decidable_eq Task) deadlineL tsk).

Definition ad_import_task_deadline (Task : eqType)
    (deadlineR : prosa.model.task.concept.TaskDeadline Task) :
    ImportedAbsoluteDeadline.Prosa_Model_Task_Concept_TaskDeadline
      Task (ad_decidable_eq Task) :=
  ImportedAbsoluteDeadline.Prosa_Model_Task_Concept_TaskDeadline_mk
    Task (ad_decidable_eq Task)
    (fun tsk => sub_nat_to_imported
      (@prosa.model.task.concept.task_deadline Task deadlineR tsk)).

Definition ad_export_task_deadline (Task : eqType)
    (deadlineL : ImportedAbsoluteDeadline.Prosa_Model_Task_Concept_TaskDeadline
      Task (ad_decidable_eq Task)) :
    prosa.model.task.concept.TaskDeadline Task :=
  fun tsk => sub_nat_to_rocq
    (ImportedAbsoluteDeadline.Prosa_Model_Task_Concept_TaskDeadline_task_deadline
      Task (ad_decidable_eq Task) deadlineL tsk).

Lemma ad_task_deadline_import_certificate (Task : eqType)
    (deadlineR : prosa.model.task.concept.TaskDeadline Task) :
  AdTaskDeadlineRel Task deadlineR
    (ad_import_task_deadline Task deadlineR).
Proof. intro tsk. exact (sub_nat_rel_canonical _). Qed.

Lemma ad_task_deadline_export_certificate (Task : eqType)
    (deadlineL : ImportedAbsoluteDeadline.Prosa_Model_Task_Concept_TaskDeadline
      Task (ad_decidable_eq Task)) :
  AdTaskDeadlineRel Task
    (ad_export_task_deadline Task deadlineL) deadlineL.
Proof. intro tsk. exact (sub_nat_rel_surjective _). Qed.

Definition AdJobArrivalRel (Job : eqType)
    (arrivalR : prosa.behavior.job.JobArrival Job)
    (arrivalL : ImportedAbsoluteDeadline.Prosa_Behavior_Job_JobArrival
      Job (ad_decidable_eq Job)) : SProp :=
  forall j : Job,
    SubNatRel (@prosa.behavior.job.job_arrival Job arrivalR j)
      (ImportedAbsoluteDeadline.Prosa_Behavior_Job_JobArrival_job_arrival
        Job (ad_decidable_eq Job) arrivalL j).

Definition ad_import_job_arrival (Job : eqType)
    (arrivalR : prosa.behavior.job.JobArrival Job) :
    ImportedAbsoluteDeadline.Prosa_Behavior_Job_JobArrival
      Job (ad_decidable_eq Job) :=
  ImportedAbsoluteDeadline.Prosa_Behavior_Job_JobArrival_mk
    Job (ad_decidable_eq Job)
    (fun j => sub_nat_to_imported
      (@prosa.behavior.job.job_arrival Job arrivalR j)).

Definition ad_export_job_arrival (Job : eqType)
    (arrivalL : ImportedAbsoluteDeadline.Prosa_Behavior_Job_JobArrival
      Job (ad_decidable_eq Job)) :
    prosa.behavior.job.JobArrival Job :=
  fun j => sub_nat_to_rocq
    (ImportedAbsoluteDeadline.Prosa_Behavior_Job_JobArrival_job_arrival
      Job (ad_decidable_eq Job) arrivalL j).

Lemma ad_job_arrival_import_certificate (Job : eqType)
    (arrivalR : prosa.behavior.job.JobArrival Job) :
  AdJobArrivalRel Job arrivalR (ad_import_job_arrival Job arrivalR).
Proof. intro j. exact (sub_nat_rel_canonical _). Qed.

Lemma ad_job_arrival_export_certificate (Job : eqType)
    (arrivalL : ImportedAbsoluteDeadline.Prosa_Behavior_Job_JobArrival
      Job (ad_decidable_eq Job)) :
  AdJobArrivalRel Job (ad_export_job_arrival Job arrivalL) arrivalL.
Proof. intro j. exact (sub_nat_rel_surjective _). Qed.

Definition AdJobDeadlineRel (Job : eqType)
    (deadlineR : prosa.behavior.job.JobDeadline Job)
    (deadlineL : ImportedAbsoluteDeadline.Prosa_Behavior_Job_JobDeadline
      Job (ad_decidable_eq Job)) : SProp :=
  forall j : Job,
    SubNatRel (@prosa.behavior.job.job_deadline Job deadlineR j)
      (ImportedAbsoluteDeadline.Prosa_Behavior_Job_JobDeadline_job_deadline
        Job (ad_decidable_eq Job) deadlineL j).

Definition ad_import_job_deadline (Job : eqType)
    (deadlineR : prosa.behavior.job.JobDeadline Job) :
    ImportedAbsoluteDeadline.Prosa_Behavior_Job_JobDeadline
      Job (ad_decidable_eq Job) :=
  ImportedAbsoluteDeadline.Prosa_Behavior_Job_JobDeadline_mk
    Job (ad_decidable_eq Job)
    (fun j => sub_nat_to_imported
      (@prosa.behavior.job.job_deadline Job deadlineR j)).

Definition ad_export_job_deadline (Job : eqType)
    (deadlineL : ImportedAbsoluteDeadline.Prosa_Behavior_Job_JobDeadline
      Job (ad_decidable_eq Job)) :
    prosa.behavior.job.JobDeadline Job :=
  fun j => sub_nat_to_rocq
    (ImportedAbsoluteDeadline.Prosa_Behavior_Job_JobDeadline_job_deadline
      Job (ad_decidable_eq Job) deadlineL j).

Lemma ad_job_deadline_import_certificate (Job : eqType)
    (deadlineR : prosa.behavior.job.JobDeadline Job) :
  AdJobDeadlineRel Job deadlineR
    (ad_import_job_deadline Job deadlineR).
Proof. intro j. exact (sub_nat_rel_canonical _). Qed.

Lemma ad_job_deadline_export_certificate (Job : eqType)
    (deadlineL : ImportedAbsoluteDeadline.Prosa_Behavior_Job_JobDeadline
      Job (ad_decidable_eq Job)) :
  AdJobDeadlineRel Job (ad_export_job_deadline Job deadlineL) deadlineL.
Proof. intro j. exact (sub_nat_rel_surjective _). Qed.

Definition ad_target_add (a b : Lean.Nat) : Lean.Nat :=
  ImportedAbsoluteDeadline.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedAbsoluteDeadline.instHAdd_inst1 Lean.Nat
      ImportedAbsoluteDeadline.instAddNat) a b.

Lemma ad_target_add_is_certified (a b : Lean.Nat) :
  Lean.eq (ad_target_add a b) (sub_imported_add a b).
Proof. exact (@Lean.eq_refl _ _). Qed.
