(* Re-bound copy of the accepted certificates/model_priority_elf/PriorityElfCorrespondence.v (helper-only:
   the file has no statement correspondences); its GEL import is the helper-only PriorityGelHelpers of this
   closure; every definition and proof is unchanged. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From mathcomp Require Import ssralg ssrnum ssrint.
From prosa Require Import model.priority.elf.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedBoundedBiElf.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence NatSubCorrespondence
  PcoBaseAdapter PcoStaticOrder PcoDynamicOrder PriorityCoercionCorrespondence
  PriorityGelHelpers.

Module I := ImportedBoundedBiElf.

(** Certificate for [model/priority/elf.v].

    [ELF fp] is related as [PdJLFPRel] under the input relations: the FP
    policy pointwise on Booleans ([PdFPRel]), the priority points by the
    accepted [GelPriorityPointRel], [job_arrival] pointwise on Nat and
    [job_task] by [Lean.eq].  The strict task priority [hp_task] is related
    through the Boolean connectives and the GEL tie-breaker through the
    accepted [GEL_correspondence]. *)

Section Policy.
  Context (Job Task : eqType).
  Let dJ := pd_decidable_eq Job.
  Let dT := pd_decidable_eq Task.
  Variable ppR : prosa.model.priority.gel.PriorityPoint Task.
  Variable ppL : I.Prosa_Model_Priority_Gel_PriorityPoint Task dT.
  Hypothesis Hpp : GelPriorityPointRel Task ppR ppL.
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_arrival Job jaR j)
      (I.Prosa_Behavior_Job_JobArrival_job_arrival Job dJ jaL j).
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Variable fpR : prosa.model.priority.definitions.FP_policy Task.
  Variable fpL : I.Prosa_Model_Priority_Definitions_FP_policy Task dT.
  Hypothesis Hfp : PdFPRel Task fpR fpL.

  Lemma elf_hep_task_related (x y : Job) :
    PdBoolRel
      (@prosa.model.priority.definitions.hep_task Task fpR
        (@prosa.model.task.concept.job_task Job Task jtR x)
        (@prosa.model.task.concept.job_task Job Task jtR y))
      (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fpL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL x)
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL y)).
  Proof.
    unfold PdBoolRel.
    exact (sub_imported_eq_trans _ _ _ (Hfp _ _)
      (sub_imported_eq_congr2
        (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fpL) _ _ _ _
        (Hjt x) (Hjt y))).
  Qed.

  Lemma elf_hp_task_related (x y : Job) :
    PdBoolRel
      (@prosa.model.priority.definitions.hp_task Task fpR
        (@prosa.model.task.concept.job_task Job Task jtR x)
        (@prosa.model.task.concept.job_task Job Task jtR y))
      (I.Prosa_Model_Priority_Definitions_hp_task Task dT fpL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL x)
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL y)).
  Proof.
    unfold prosa.model.priority.definitions.hp_task.
    cbn [I.Prosa_Model_Priority_Definitions_hp_task].
    exact (pd_bool_and_related _ _ _ _ (elf_hep_task_related x y)
      (pd_bool_not_related _ _ (elf_hep_task_related y x))).
  Qed.

  Theorem ELF_correspondence :
    PdJLFPRel Job (@prosa.model.priority.elf.ELF Task ppR Job jaR jtR fpR)
      (I.Prosa_Model_Priority_Elf_ELF Task dT ppL Job dJ jaL jtL fpL).
  Proof.
    intros x y. cbn.
    exact (pd_bool_or_related _ _ _ _ (elf_hp_task_related x y)
      (pd_bool_and_related _ _ _ _ (elf_hep_task_related x y)
        (GEL_correspondence Job Task ppR ppL Hpp jaR jaL Hja jtR jtL Hjt x y))).
  Qed.
End Policy.
