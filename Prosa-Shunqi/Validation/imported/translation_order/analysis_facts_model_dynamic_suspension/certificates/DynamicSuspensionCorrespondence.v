(* Copy of the accepted certificates/model_task_suspension_dynamic/DynamicSuspensionCorrespondence.v, re-bound to
   this export; only the imported module name differs. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import DynamicSuspensionSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsDynamicSuspension ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations ProgressHelpers
  SuspensionCorrespondence.

Module I := ImportedFactsDynamicSuspension.
Module S := DynamicSuspensionSemanticSource.DynamicSuspensionSemanticSource.

(** Correspondences for [model/task/suspension/dynamic.v].  The class
    [TaskTotalSuspension] is related pointwise by [SubNatRel]; every source
    instance has a related compiled instance and conversely.  For related
    job-cost, job-suspension, job-task and task-total-suspension instances,
    the extracted validity definition and the compiled Lean definition are
    related; the job-task relation is Lean equality on the identity task
    carrier, with import and export witnesses. *)

Lemma dsusp_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Section DynamicSuspension.
  Context (Task : eqType).
  Let dT := svc_decidable_eq Task.

  Definition DsuspTaskTotalSuspensionRel (cR : S.TaskTotalSuspension Task)
      (cL : I.Prosa_Model_Task_Suspension_Dynamic_TaskTotalSuspension Task dT) : SProp :=
    forall tsk : Task, SubNatRel (@S.task_total_suspension Task cR tsk)
      (I.Prosa_Model_Task_Suspension_Dynamic_TaskTotalSuspension_task_total_suspension Task dT cL tsk).

  Lemma TaskTotalSuspension_source_total (cR : S.TaskTotalSuspension Task) :
    DsuspTaskTotalSuspensionRel cR
      (I.Prosa_Model_Task_Suspension_Dynamic_TaskTotalSuspension_mk Task dT
        (fun tsk => sub_nat_to_imported (@S.task_total_suspension Task cR tsk))).
  Proof. intro tsk. exact (@Lean.eq_refl _ _). Qed.

  Lemma TaskTotalSuspension_target_total
      (cL : I.Prosa_Model_Task_Suspension_Dynamic_TaskTotalSuspension Task dT) :
    DsuspTaskTotalSuspensionRel
      ((fun tsk => sub_nat_to_rocq
        (I.Prosa_Model_Task_Suspension_Dynamic_TaskTotalSuspension_task_total_suspension Task dT cL tsk))
        : S.TaskTotalSuspension Task) cL.
  Proof. intro tsk. exact (sub_nat_rel_surjective _). Qed.

  Context (Job : eqType).
  Let dJ := svc_decidable_eq Job.

  Definition DsuspJobTaskRel (jtR : prosa.model.task.concept.JobTask Job Task)
      (jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT) : SProp :=
    forall j : Job,
      Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).

  Lemma dsusp_job_task_import (jtR : prosa.model.task.concept.JobTask Job Task) :
    DsuspJobTaskRel jtR
      (I.Prosa_Model_Task_Concept_JobTask_mk Job dJ Task dT
        (fun j => @prosa.model.task.concept.job_task Job Task jtR j)).
  Proof. intro j. exact (@Lean.eq_refl _ _). Qed.

  Lemma dsusp_job_task_export (jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT) :
    DsuspJobTaskRel
      ((fun j => I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j)
        : prosa.model.task.concept.JobTask Job Task) jtL.
  Proof. intro j. exact (@Lean.eq_refl _ _). Qed.

  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable sR : SuspensionSemanticSource.SuspensionSemanticSource.JobSuspension Job.
  Variable sL : I.Prosa_Model_Readiness_Suspension_JobSuspension Job dJ.
  Hypothesis Hs : SuspJobSuspensionRel Job sR sL.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : DsuspJobTaskRel jtR jtL.
  Variable ttsR : S.TaskTotalSuspension Task.
  Variable ttsL : I.Prosa_Model_Task_Suspension_Dynamic_TaskTotalSuspension Task dT.
  Hypothesis Htts : DsuspTaskTotalSuspensionRel ttsR ttsL.

  Lemma dsusp_task_bound_related (j : Job) :
    SubNatRel (@S.task_total_suspension Task ttsR (@prosa.model.task.concept.job_task Job Task jtR j))
      (I.Prosa_Model_Task_Suspension_Dynamic_TaskTotalSuspension_task_total_suspension Task dT ttsL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j)).
  Proof.
    exact (dsusp_lean_transport (fun v => SubNatRel
      (@S.task_total_suspension Task ttsR (@prosa.model.task.concept.job_task Job Task jtR j))
      (I.Prosa_Model_Task_Suspension_Dynamic_TaskTotalSuspension_task_total_suspension Task dT ttsL v))
      _ _ (Hjt j) (Htts _)).
  Qed.

  Theorem valid_dynamic_suspensions_correspondence :
    PropSPropRel (@S.valid_dynamic_suspensions Job costR sR Task jtR ttsR)
      (I.Prosa_Model_Task_Suspension_Dynamic_valid_dynamic_suspensions Job dJ costL sL Task dT jtL ttsL).
  Proof.
    unfold S.valid_dynamic_suspensions.
    cbn [I.Prosa_Model_Task_Suspension_Dynamic_valid_dynamic_suspensions].
    apply pg_forall_identity_correspondence. intro j.
    exact (sub_nat_le_correspondence _ _ _ _
      (total_suspension_correspondence Job costR costL Hcost sR sL Hs j)
      (dsusp_task_bound_related j)).
  Qed.
End DynamicSuspension.
