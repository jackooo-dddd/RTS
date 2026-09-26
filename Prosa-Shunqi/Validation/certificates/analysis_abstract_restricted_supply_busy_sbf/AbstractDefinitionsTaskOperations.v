(* Re-bound copy of accepted imported/translation_order/abstract_definitions/certificates/AbstractDefinitionsTaskOperations.v for the busy_sbf artifact; only the imported module name differs. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import model.task.concept.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedBusySbf.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence AbstractDefinitionsBaseAdapter
  ServiceBaseAdapter ServiceNatBoolOperations.

(** The accepted JobTask pattern is instantiated again at this actual
    imported artifact.  The field relation is an input representation
    relation, not an unproved equality of the two [job_of_task] operations. *)
Definition AdJobTaskRel (Job Task : eqType)
    (src : prosa.model.task.concept.JobTask Job Task)
    (dst : ImportedBusySbf.Prosa_Model_Task_Concept_JobTask
      Job (ad_decidable_eq Job) Task (ad_decidable_eq Task)) : SProp :=
  forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task src j)
      (ImportedBusySbf.Prosa_Model_Task_Concept_JobTask_job_task
        Job (ad_decidable_eq Job) Task (ad_decidable_eq Task) dst j).

Definition ad_import_job_task (Job Task : eqType)
    (src : prosa.model.task.concept.JobTask Job Task) :
    ImportedBusySbf.Prosa_Model_Task_Concept_JobTask
      Job (ad_decidable_eq Job) Task (ad_decidable_eq Task) :=
  ImportedBusySbf.Prosa_Model_Task_Concept_JobTask_mk
    Job (ad_decidable_eq Job) Task (ad_decidable_eq Task)
    (fun j => @prosa.model.task.concept.job_task Job Task src j).

Definition ad_export_job_task (Job Task : eqType)
    (dst : ImportedBusySbf.Prosa_Model_Task_Concept_JobTask
      Job (ad_decidable_eq Job) Task (ad_decidable_eq Task)) :
    prosa.model.task.concept.JobTask Job Task :=
  fun j => ImportedBusySbf.Prosa_Model_Task_Concept_JobTask_job_task
    Job (ad_decidable_eq Job) Task (ad_decidable_eq Task) dst j.

Lemma ad_job_task_import_certificate (Job Task : eqType)
    (src : prosa.model.task.concept.JobTask Job Task) :
  AdJobTaskRel Job Task src (ad_import_job_task Job Task src).
Proof. intro j. exact (@Lean.eq_refl _ _). Qed.

Lemma ad_job_task_export_certificate (Job Task : eqType)
    (dst : ImportedBusySbf.Prosa_Model_Task_Concept_JobTask
      Job (ad_decidable_eq Job) Task (ad_decidable_eq Task)) :
  AdJobTaskRel Job Task (ad_export_job_task Job Task dst) dst.
Proof. intro j. exact (@Lean.eq_refl _ _). Qed.

Definition ad_target_decide_eq (Task : eqType) (x y : Task) :
    ImportedBusySbf.Bool :=
  ImportedBusySbf.Decidable_decide (Lean.eq x y)
    (ad_decidable_eq Task x y).

Lemma ad_task_eq_bool_related (Task : eqType) (x y : Task) :
  AdBoolRel (x == y) (ad_target_decide_eq Task x y).
Proof.
  apply svc_decide_bool_correspondence.
  apply prop_sprop_rel_intro.
  - move/eqP => Heq. exact (coq_eq_to_imported_eq x y Heq).
  - intro Heq. apply strictly_inhabits. apply/eqP.
    exact (imported_eq_to_coq_eq x y Heq).
Qed.

Lemma ad_job_of_task_related (Job Task : eqType)
    (src : prosa.model.task.concept.JobTask Job Task)
    (dst : ImportedBusySbf.Prosa_Model_Task_Concept_JobTask
      Job (ad_decidable_eq Job) Task (ad_decidable_eq Task))
    (tsk : Task) (j : Job) :
  AdJobTaskRel Job Task src dst ->
  AdBoolRel (@prosa.model.task.concept.job_of_task Job Task src tsk j)
    (ImportedBusySbf.Prosa_Model_Task_Concept_job_of_task
      Job (ad_decidable_eq Job) Task (ad_decidable_eq Task) dst tsk j).
Proof.
  intro Hfield.
  cbn [ImportedBusySbf.Prosa_Model_Task_Concept_job_of_task].
  exact (sub_imported_eq_trans _ _ _
    (ad_task_eq_bool_related Task
      (@prosa.model.task.concept.job_task Job Task src j) tsk)
    (sub_imported_eq_congr
      (fun t => ad_target_decide_eq Task t tsk) _ _ (Hfield j))).
Qed.

Print Assumptions ad_job_task_import_certificate.
Print Assumptions ad_job_task_export_certificate.
Print Assumptions ad_job_of_task_related.
