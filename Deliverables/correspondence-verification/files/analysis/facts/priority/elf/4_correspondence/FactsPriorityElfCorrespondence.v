From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From mathcomp Require Import ssralg ssrnum ssrint.
From prosa Require Import FactsPriorityElfSemanticSource.
From prosa Require Import behavior.all model.processor.platform_properties model.schedule.scheduled
  model.priority.classes model.task.sequentiality analysis.definitions.work_bearing_readiness
  analysis.definitions.priority.classes util.int model.priority.gel model.priority.elf.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsPriorityElf ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers
  NatSubCorrespondence PcoBaseAdapter PcoStaticOrder PcoDynamicOrder PriorityCoercionCorrespondence
  PriorityGelHelpers PriorityElfHelpers.

Module I := ImportedFactsPriorityElf.
Module S := FactsPriorityElfSemanticSource.FactsPriorityElfSemanticSource.

(** Statement correspondences for [analysis/facts/priority/elf.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs (task and job types, the priority-point, job-task,
    job-cost and arrival classes, the FP policy); target side: the imported
    Lean theorem types.  Inputs: [job_task] by [Lean.eq], task priority
    points by the accepted [GelPriorityPointRel], [job_arrival] and
    [job_cost] pointwise, the FP policy pointwise on Booleans ([PdFPRel]).
    Inputs quantified inside a statement are covered in both directions:
    arrival sequences ([fpre_forall_arr]), processor models (the accepted
    [isj_cover_pstate]), schedules through the processor-model relation
    ([fpre_forall_sched]), the readiness instance on the statement's schedule
    pair ([fpre_forall_jr]), [JobPreemptable] instances ([fpre_forall_jp]),
    tasks, jobs and instants.

    [ELF FP] and [GEL] are the accepted ELF and GEL certificates
    ([ELF_correspondence], [GEL_correspondence]); the task priorities
    ([hep_task], [hp_task] of job tasks) the accepted ELF helpers; the
    reflexivity, transitivity and totality of task and job priorities the
    accepted priority-order certificates.  Preemption models, schedule
    validity, the JLFP policy at preemption points and the
    scheduled/completion observations are the accepted preemption-facts
    helpers; work-bearing readiness, the JLFP/FP compatibility and sequential
    tasks are related by unfolding.  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma felf_exists_identity (T : Type) (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (exists x, PR x) (I.Exists T PL).
Proof.
  intro H. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (I.Exists_intro T PL x (prop_to_sprop _ _ (H x) Hx)).
  - intros [x Hx]. apply strictly_inhabits. exists x. exact (sprop_to_prop _ _ (H x) Hx).
Qed.

Section Elf.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
  Variable ppR : prosa.model.priority.gel.PriorityPoint Task.
  Variable ppL : I.Prosa_Model_Priority_Gel_PriorityPoint Task dT.
  Hypothesis Hpp : GelPriorityPointRel Task ppR ppL.
  Variable jtR : prosa.model.task.concept.JobTask Job Task.
  Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
  Hypothesis Hjt : forall j : Job,
    Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_arrival Job jaR j)
      (I.Prosa_Behavior_Job_JobArrival_job_arrival Job dJ jaL j).
  Variable fpR : prosa.model.priority.definitions.FP_policy Task.
  Variable fpL : I.Prosa_Model_Priority_Definitions_FP_policy Task dT.
  Hypothesis Hfp : PdFPRel Task fpR fpL.

  Let ER := @prosa.model.priority.elf.ELF Task ppR Job jaR jtR fpR.
  Let EL := I.Prosa_Model_Priority_Elf_ELF Task dT ppL Job dJ jaL jtL fpL.
  Let GR := @prosa.model.priority.gel.GEL Job Task ppR jaR jtR.
  Let GL := I.Prosa_Model_Priority_Gel_GEL Job dJ Task dT ppL jaL jtL.

  Lemma felf_elf_rel : PdJLFPRel Job ER EL.
  Proof. exact (ELF_correspondence Job Task ppR ppL Hpp jaR jaL Hja jtR jtL Hjt fpR fpL Hfp). Qed.

  Lemma felf_gel_rel : PdJLFPRel Job GR GL.
  Proof. exact (GEL_correspondence Job Task ppR ppL Hpp jaR jaL Hja jtR jtL Hjt). Qed.

  Lemma felf_hep_task_related (x y : Job) :
    PdBoolRel
      (@prosa.model.priority.definitions.hep_task Task fpR
        (@prosa.model.task.concept.job_task Job Task jtR x) (@prosa.model.task.concept.job_task Job Task jtR y))
      (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fpL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL x)
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL y)).
  Proof. exact (elf_hep_task_related Job Task jtR jtL Hjt fpR fpL Hfp x y). Qed.

  Lemma felf_hp_task_related (x y : Job) :
    PdBoolRel
      (@prosa.model.priority.definitions.hp_task Task fpR
        (@prosa.model.task.concept.job_task Job Task jtR x) (@prosa.model.task.concept.job_task Job Task jtR y))
      (I.Prosa_Model_Priority_Definitions_hp_task Task dT fpL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL x)
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL y)).
  Proof. exact (elf_hp_task_related Job Task jtR jtL Hjt fpR fpL Hfp x y). Qed.

  Lemma felf_ep_task_related (x y : Job) :
    PdBoolRel
      (@prosa.model.priority.definitions.ep_task Task fpR
        (@prosa.model.task.concept.job_task Job Task jtR x) (@prosa.model.task.concept.job_task Job Task jtR y))
      (I.Prosa_Model_Priority_Definitions_ep_task Task dT fpL
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL x)
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL y)).
  Proof.
    unfold prosa.model.priority.definitions.ep_task. cbn [I.Prosa_Model_Priority_Definitions_ep_task].
    exact (pd_bool_and_related _ _ _ _ (felf_hep_task_related x y) (felf_hep_task_related y x)).
  Qed.

  Lemma felf_same_task_related (x y : Job) :
    ArBoolRel (@prosa.model.task.concept.same_task Job Task jtR x y)
      (I.Prosa_Model_Task_Concept_same_task Job dJ Task dT jtL x y).
  Proof.
    unfold prosa.model.task.concept.same_task. cbn [I.Prosa_Model_Task_Concept_same_task].
    exact (pd_eq_observation_transport Task _ _ _ _ (Hjt x) (Hjt y)).
  Qed.

  Let reflR := pd_reflexive_task_priorities_certificate Task fpR fpL Hfp.
  Let transR := pd_transitive_task_priorities_certificate Task fpR fpL Hfp.
  Let totR := pd_total_task_priorities_certificate Task fpR fpL Hfp.

  (** *** hep_job_elf_gel *)

  Definition src_hep_job_elf_gel : Prop :=
    ltac:(body_of (fun s : S.statement_hep_job_elf_gel => s Task ppR Job jtR jaR fpR)).
  Definition tgt_hep_job_elf_gel : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Elf_hep_job_elf_gel Task dT Job dJ ppL jtL jaL fpL)).

  Theorem hep_job_elf_gel_correspondence : PropSPropRel src_hep_job_elf_gel tgt_hep_job_elf_gel.
  Proof.
    unfold src_hep_job_elf_gel, tgt_hep_job_elf_gel.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_identity_correspondence. intro j'.
    apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (felf_ep_task_related j j'))|].
    exact (ar_bool_eq_correspondence _ _ _ _ (felf_elf_rel j j') (felf_gel_rel j j')).
  Qed.

  (** *** hep_job_arrival_elf *)

  Definition src_hep_job_arrival_elf : Prop :=
    ltac:(body_of (fun s : S.statement_hep_job_arrival_elf => s Task ppR Job jtR jaR fpR)).
  Definition tgt_hep_job_arrival_elf : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Elf_hep_job_arrival_elf Task dT Job dJ ppL jtL jaL fpL)).

  Theorem hep_job_arrival_elf_correspondence : PropSPropRel src_hep_job_arrival_elf tgt_hep_job_arrival_elf.
  Proof.
    unfold src_hep_job_arrival_elf, tgt_hep_job_arrival_elf.
    apply ar_imp_correspondence; [exact reflR|].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_identity_correspondence. intro j'.
    apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (felf_same_task_related j j'))|].
    exact (ar_bool_eq_correspondence _ _ _ _ (felf_elf_rel j j') (svc_decide_le_related _ _ _ _ (Hja j) (Hja j'))).
  Qed.

  (** *** Order properties of ELF *)

  Definition src_ELF_is_reflexive : Prop :=
    ltac:(body_of (fun s : S.statement_ELF_is_reflexive => s Task ppR Job jtR jaR fpR)).
  Definition tgt_ELF_is_reflexive : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Elf_ELF_is_reflexive Task dT Job dJ ppL jtL jaL fpL)).

  Theorem ELF_is_reflexive_correspondence : PropSPropRel src_ELF_is_reflexive tgt_ELF_is_reflexive.
  Proof.
    unfold src_ELF_is_reflexive, tgt_ELF_is_reflexive.
    apply ar_imp_correspondence; [exact reflR|].
    exact (pd_reflexive_job_priorities_certificate Job _ _ felf_elf_rel).
  Qed.

  Definition src_ELF_is_transitive : Prop :=
    ltac:(body_of (fun s : S.statement_ELF_is_transitive => s Task ppR Job jtR jaR fpR)).
  Definition tgt_ELF_is_transitive : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Elf_ELF_is_transitive Task dT Job dJ ppL jtL jaL fpL)).

  Theorem ELF_is_transitive_correspondence : PropSPropRel src_ELF_is_transitive tgt_ELF_is_transitive.
  Proof.
    unfold src_ELF_is_transitive, tgt_ELF_is_transitive.
    apply ar_imp_correspondence; [exact transR|].
    exact (pd_transitive_job_priorities_certificate Job _ _ felf_elf_rel).
  Qed.

  Definition src_ELF_is_total : Prop :=
    ltac:(body_of (fun s : S.statement_ELF_is_total => s Task ppR Job jtR jaR fpR)).
  Definition tgt_ELF_is_total : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Elf_ELF_is_total Task dT Job dJ ppL jtL jaL fpL)).

  Theorem ELF_is_total_correspondence : PropSPropRel src_ELF_is_total tgt_ELF_is_total.
  Proof.
    unfold src_ELF_is_total, tgt_ELF_is_total.
    apply ar_imp_correspondence; [exact totR|].
    exact (pd_total_job_priorities_certificate Job _ _ felf_elf_rel).
  Qed.

  Definition src_ELF_is_JLFP_FP_compatible : Prop :=
    ltac:(body_of (fun s : S.statement_ELF_is_JLFP_FP_compatible => s Task ppR Job jtR jaR fpR)).
  Definition tgt_ELF_is_JLFP_FP_compatible : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Elf_ELF_is_JLFP_FP_compatible Task dT Job dJ ppL jtL jaL fpL)).

  Theorem ELF_is_JLFP_FP_compatible_correspondence :
    PropSPropRel src_ELF_is_JLFP_FP_compatible tgt_ELF_is_JLFP_FP_compatible.
  Proof.
    unfold src_ELF_is_JLFP_FP_compatible, tgt_ELF_is_JLFP_FP_compatible.
    unfold prosa.analysis.definitions.priority.classes.JLFP_FP_compatible.
    cbn [I.Prosa_Analysis_Definitions_Priority_Classes_JLFP_FP_compatible].
    apply ar_and_correspondence.
    - apply ar_forall_identity_correspondence. intro j1.
      apply ar_forall_identity_correspondence. intro j2.
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (felf_elf_rel j1 j2))|].
      exact (ar_bool_truth_correspondence _ _ (felf_hep_task_related j1 j2)).
    - apply ar_forall_identity_correspondence. intro j1.
      apply ar_forall_identity_correspondence. intro j2.
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (felf_hp_task_related j1 j2))|].
      exact (ar_bool_truth_correspondence _ _ (felf_elf_rel j1 j2)).
  Qed.

  (** *** Sequentiality *)

  Definition src_ELF_respects_sequential_tasks : Prop :=
    ltac:(body_of (fun s : S.statement_ELF_respects_sequential_tasks => s Task ppR Job jtR jaR fpR)).
  Definition tgt_ELF_respects_sequential_tasks : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Elf_ELF_respects_sequential_tasks Task dT Job dJ ppL jtL jaL fpL)).

  Theorem ELF_respects_sequential_tasks_correspondence :
    PropSPropRel src_ELF_respects_sequential_tasks tgt_ELF_respects_sequential_tasks.
  Proof.
    unfold src_ELF_respects_sequential_tasks, tgt_ELF_respects_sequential_tasks.
    apply ar_imp_correspondence; [exact reflR|].
    unfold prosa.model.priority.definitions.policy_respects_sequential_tasks.
    cbn [I.Prosa_Model_Priority_Definitions_policy_respects_sequential_tasks].
    apply ar_forall_identity_correspondence. intro j1.
    apply ar_forall_identity_correspondence. intro j2.
    apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (felf_same_task_related j1 j2))|].
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ (Hja j1) (Hja j2))|].
    exact (ar_bool_truth_correspondence _ _ (felf_elf_rel j1 j2)).
  Qed.

  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.

  Section Pair.
    Variable PR : prosa.behavior.schedule.ProcessorState Job.
    Variable PL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
    Variable X : IsjPSRel Job PR PL.
    Variable sR : @prosa.behavior.schedule.schedule Job PR.
    Variable sL : I.Prosa_Behavior_Schedule_schedule Job dJ PL.
    Hypothesis Hs : IsjPSchedRel Job PR PL X sR sL.
    Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
    Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
    Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

    Let Hsa := isj_psr_scheduled_at_related Job PR PL X sR sL Hs.

    Lemma felf_sequential_tasks_rel :
      PropSPropRel (@prosa.model.task.sequentiality.sequential_tasks Job Task jtR jaR costR PR arrR sR)
        (I.Prosa_Model_Task_Sequentiality_sequential_tasks Job dJ Task dT jtL jaL costL PL arrL sL).
    Proof.
      unfold prosa.model.task.sequentiality.sequential_tasks.
      cbn [I.Prosa_Model_Task_Sequentiality_sequential_tasks].
      apply ar_forall_identity_correspondence. intro j1.
      apply ar_forall_identity_correspondence. intro j2.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j1 Harr)|].
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j2 Harr)|].
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (felf_same_task_related j1 j2))|].
      apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ (Hja j1) (Hja j2))|].
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hsa j2 _ _ Ht))|].
      exact (ar_bool_truth_correspondence _ _
        (fpre_completed_by_related Job costR costL Hcost PR PL X sR sL Hs j1 tR tL Ht)).
    Qed.

    Section Ready.
      Variable jrR : @prosa.behavior.ready.JobReady Job PR costR jaR.
      Variable jrL : I.Prosa_Behavior_Ready_JobReady Job dJ PL costL jaL.
      Hypothesis Hjr : FpreJrAt Job jaR jaL costR costL PR PL sR sL jrR jrL.

      Lemma felf_work_bearing_rel :
        PropSPropRel
          (@prosa.analysis.definitions.work_bearing_readiness.work_bearing_readiness
            Job jaR costR PR jrR arrR sR ER)
          (I.Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness
            Job dJ jaL costL PL jrL arrL sL EL).
      Proof.
        unfold prosa.analysis.definitions.work_bearing_readiness.work_bearing_readiness.
        cbn [I.Prosa_Analysis_Definitions_WorkBearingReadiness_work_bearing_readiness].
        apply ar_forall_identity_correspondence. intro j.
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
        apply ar_imp_correspondence;
          [exact (ar_bool_truth_correspondence _ _
            (fpre_pending_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs j tR tL Ht))|].
        apply felf_exists_identity. intro jhp.
        apply ar_and_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL jhp Harr)|].
        apply ar_and_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hjr jhp tR tL Ht))|].
        exact (ar_bool_truth_correspondence _ _ (felf_elf_rel jhp j)).
      Qed.
    End Ready.
  End Pair.

  Definition src_ELF_implies_sequential_tasks : Prop :=
    ltac:(body_of (fun s : S.statement_ELF_implies_sequential_tasks => s Task ppR Job jtR costR jaR fpR)).
  Definition tgt_ELF_implies_sequential_tasks : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Elf_ELF_implies_sequential_tasks
      Task dT Job dJ ppL jtL costL jaL fpL)).

  Theorem ELF_implies_sequential_tasks_correspondence :
    PropSPropRel src_ELF_implies_sequential_tasks tgt_ELF_implies_sequential_tasks.
  Proof.
    unfold src_ELF_implies_sequential_tasks, tgt_ELF_implies_sequential_tasks.
    apply ar_imp_correspondence; [exact reflR|].
    apply ar_imp_correspondence; [exact transR|].
    apply fpre_forall_arr. intros arrR arrL Harr.
    apply ar_imp_correspondence;
      [exact (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr)|].
    apply (isj_cover_pstate Job). intros PR PL X.
    apply ar_imp_correspondence; [exact (isj_psr_uniprocessor_related Job PR PL X)|].
    apply (fpre_forall_sched Job PR PL X). intros sR sL Hs.
    apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs). intros jrR jrL Hjr.
    apply ar_imp_correspondence;
      [exact (felf_work_bearing_rel PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr)|].
    apply ar_imp_correspondence;
      [exact (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr)|].
    apply (fpre_forall_jp Job). intros jpR jpL Hjp.
    apply ar_imp_correspondence;
      [exact (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL Harr jpR jpL Hjp)|].
    apply ar_imp_correspondence;
      [exact (fpre_respects_jlfp_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr
        jpR jpL Hjp ER EL felf_elf_rel)|].
    exact (felf_sequential_tasks_rel PR PL X sR sL Hs arrR arrL Harr).
  Qed.

End Elf.
