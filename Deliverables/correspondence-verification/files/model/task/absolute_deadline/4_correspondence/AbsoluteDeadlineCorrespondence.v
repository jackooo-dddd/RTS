From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From prosa Require Import model.task.absolute_deadline.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedAbsoluteDeadline.
From FoundationCertificates Require Import LogicalRelation
  SubadditivityNatCorrespondence.
From AbsoluteDeadlineCertificates Require Import AbsoluteDeadlineBaseAdapter.

(** The certificate composes three related class observations with the
    already certified Nat-add operation.  It unfolds both actual instance
    bodies and never invokes either instance constant as a proof. *)
Lemma ad_job_deadline_from_task_deadline_certificate
    (Job Task : eqType)
    (deadlineR : prosa.model.task.concept.TaskDeadline Task)
    (arrivalR : prosa.behavior.job.JobArrival Job)
    (jobTaskR : prosa.model.task.concept.JobTask Job Task)
    (deadlineL : ImportedAbsoluteDeadline.Prosa_Model_Task_Concept_TaskDeadline
      Task (ad_decidable_eq Task))
    (arrivalL : ImportedAbsoluteDeadline.Prosa_Behavior_Job_JobArrival
      Job (ad_decidable_eq Job))
    (jobTaskL : ImportedAbsoluteDeadline.Prosa_Model_Task_Concept_JobTask
      Job (ad_decidable_eq Job) Task (ad_decidable_eq Task)) :
  AdTaskDeadlineRel Task deadlineR deadlineL ->
  AdJobArrivalRel Job arrivalR arrivalL ->
  AdJobTaskRel Job Task jobTaskR jobTaskL ->
  AdJobDeadlineRel Job
    (@prosa.model.task.absolute_deadline.job_deadline_from_task_deadline
      Job Task deadlineR arrivalR jobTaskR)
    (ImportedAbsoluteDeadline.Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline
      Job Task (ad_decidable_eq Job) (ad_decidable_eq Task)
      deadlineL arrivalL jobTaskL).
Proof.
  intros Hdeadline Harrival HjobTask j.
  cbn [AdJobDeadlineRel
    prosa.model.task.absolute_deadline.job_deadline_from_task_deadline
    ImportedAbsoluteDeadline.Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline
    prosa.behavior.job.job_deadline
    ImportedAbsoluteDeadline.Prosa_Behavior_Job_JobDeadline_job_deadline].
  set (aL := ImportedAbsoluteDeadline.Prosa_Behavior_Job_JobArrival_job_arrival
    Job (ad_decidable_eq Job) arrivalL j).
  set (sR := @prosa.model.task.concept.job_task Job Task jobTaskR j).
  set (sL := ImportedAbsoluteDeadline.Prosa_Model_Task_Concept_JobTask_job_task
    Job (ad_decidable_eq Job) Task (ad_decidable_eq Task) jobTaskL j).
  set (dL := fun tsk : Task =>
    ImportedAbsoluteDeadline.Prosa_Model_Task_Concept_TaskDeadline_task_deadline
      Task (ad_decidable_eq Task) deadlineL tsk).
  unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_add_correspondence
      (@prosa.behavior.job.job_arrival Job arrivalR j) aL
      (@prosa.model.task.concept.task_deadline Task deadlineR sR) (dL sR)
      (Harrival j) (Hdeadline sR))
    (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _ (ad_target_add_is_certified aL (dL sR)))
      (sub_imported_eq_congr (fun tsk => ad_target_add aL (dL tsk))
        sR sL (HjobTask j)))).
Qed.

Lemma ad_job_deadline_from_task_deadline_canonical
    (Job Task : eqType)
    (deadlineR : prosa.model.task.concept.TaskDeadline Task)
    (arrivalR : prosa.behavior.job.JobArrival Job)
    (jobTaskR : prosa.model.task.concept.JobTask Job Task) :
  AdJobDeadlineRel Job
    (@prosa.model.task.absolute_deadline.job_deadline_from_task_deadline
      Job Task deadlineR arrivalR jobTaskR)
    (ImportedAbsoluteDeadline.Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline
      Job Task (ad_decidable_eq Job) (ad_decidable_eq Task)
      (ad_import_task_deadline Task deadlineR)
      (ad_import_job_arrival Job arrivalR)
      (ad_import_job_task Job Task jobTaskR)).
Proof.
  exact (ad_job_deadline_from_task_deadline_certificate
    Job Task deadlineR arrivalR jobTaskR
    (ad_import_task_deadline Task deadlineR)
    (ad_import_job_arrival Job arrivalR)
    (ad_import_job_task Job Task jobTaskR)
    (ad_task_deadline_import_certificate Task deadlineR)
    (ad_job_arrival_import_certificate Job arrivalR)
    (ad_job_task_import_certificate Job Task jobTaskR)).
Qed.

Print Assumptions ad_job_deadline_from_task_deadline_certificate.
Print Assumptions ad_job_deadline_from_task_deadline_canonical.
