From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From mathcomp Require Import ssralg ssrnum ssrint.
From prosa Require Import GeneralityElfSemanticSource.
From prosa Require Import behavior.all model.processor.platform_properties model.schedule.scheduled
  model.priority.classes model.task.sequentiality util.int model.priority.gel model.priority.elf.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedGeneralityElf ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers
  NatSubCorrespondence PcoBaseAdapter PcoStaticOrder PcoDynamicOrder PriorityCoercionCorrespondence
  PriorityGelHelpers PriorityElfHelpers.

Module I := ImportedGeneralityElf.
Module S := GeneralityElfSemanticSource.GeneralityElfSemanticSource.
Module PDS := PriorityDrivenSemanticSource.PriorityDrivenSemanticSource.
Module PP := PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.

(** Statement correspondences for [results/generality/elf.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs (task and job types, the priority-point and
    job-task classes, the processor model, the arrival, cost, preemption and
    readiness models, the FP policy); target side: the imported Lean theorem
    types.  Inputs: processor states by the accepted two-sided
    [SvcProcessorStateRel]; [job_task] by [Lean.eq]; task priority points by
    the accepted [GelPriorityPointRel]; [job_arrival] and [job_cost]
    pointwise; [JobPreemptable] by the accepted [PpJobPreemptableRel]; the
    readiness model pointwise on Booleans at related schedules (the input
    relation of the accepted priority-driven certificate); the FP policy by
    the accepted [PdFPRel].  Schedules (through the state relation), arrival
    sequences, tasks, jobs and instants are covered in both directions.

    [ELF fp] and [GEL] are the accepted ELF and GEL certificates; the JLFP
    and FP policies at preemption points are the accepted priority-driven
    certificate; scheduled and completion observations the accepted
    preemption-parameter certificate; equal task priority and task
    inequality the accepted priority-order observations; schedule validity
    and sequential tasks are related by unfolding.  No source or target
    theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** The iff connective (as in the accepted delay-propagation certificate). *)
Lemma gelf_iff_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL -> PropSPropRel (P <-> Q) (I.Iff PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [Hpq Hqp]. apply I.Iff_intro.
    + intro p. exact (prop_to_sprop _ _ HQ (Hpq (sprop_to_prop _ _ HP p))).
    + intro q. exact (prop_to_sprop _ _ HP (Hqp (sprop_to_prop _ _ HQ q))).
  - intros [Hpq Hqp]. apply strictly_inhabits. split.
    + intro p. exact (sprop_to_prop _ _ HQ (Hpq (prop_to_sprop _ _ HP p))).
    + intro q. exact (sprop_to_prop _ _ HP (Hqp (prop_to_sprop _ _ HQ q))).
Qed.

Section Generality.
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
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_arrival Job jaR j)
      (I.Prosa_Behavior_Job_JobArrival_job_arrival Job dJ jaL j).
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable jpR : PP.JobPreemptable Job.
  Variable jpL : I.Prosa_Model_Preemption_Parameter_JobPreemptable Job dJ.
  Hypothesis Hjp : PpJobPreemptableRel Job jpR jpL.
  Variable jrR : @prosa.behavior.ready.JobReady Job PStateR costR jaR.
  Variable jrL : I.Prosa_Behavior_Ready_JobReady Job dJ PStateL costL jaL.
  Hypothesis Hjr : forall schedR schedL, SvcScheduleRel Job PStateR PStateL R schedR schedL ->
    forall (j : Job) (tR : nat) (tL : Lean.Nat), SubNatRel tR tL ->
      ArBoolRel (@prosa.behavior.ready.job_ready Job PStateR costR jaR jrR schedR j tR)
        (I.Prosa_Behavior_Ready_JobReady_job_ready Job dJ PStateL costL jaL jrL schedL j tL).
  Variable fpR : prosa.model.priority.definitions.FP_policy Task.
  Variable fpL : I.Prosa_Model_Priority_Definitions_FP_policy Task dT.
  Hypothesis Hfp : PdFPRel Task fpR fpL.

  Let SchedR := @prosa.behavior.schedule.schedule Job PStateR.
  Let SchedL := I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Let ER := @prosa.model.priority.elf.ELF Task ppR Job jaR jtR fpR.
  Let EL := I.Prosa_Model_Priority_Elf_ELF Task dT ppL Job dJ jaL jtL fpL.
  Let GR := @prosa.model.priority.gel.GEL Job Task ppR jaR jtR.
  Let GL := I.Prosa_Model_Priority_Gel_GEL Job dJ Task dT ppL jaL jtL.

  (** *** Covers *)

  Definition gelf_sched_to_target (sR : SchedR) : SchedL :=
    fun tL => svc_ps_state_to_target Job PStateR PStateL R (sR (sub_nat_to_rocq tL)).
  Definition gelf_sched_to_source (sL : SchedL) : SchedR :=
    fun tR => svc_ps_state_to_source Job PStateR PStateL R (sL (sub_nat_to_imported tR)).

  Lemma gelf_forall_sched (PR : SchedR -> Prop) (PL : SchedL -> SProp) :
    (forall sR sL, SvcScheduleRel Job PStateR PStateL R sR sL -> PropSPropRel (PR sR) (PL sL)) ->
    PropSPropRel (forall s, PR s) (forall s, PL s).
  Proof.
    apply (isj_forall_cover_sprop _ _ (SvcScheduleRel Job PStateR PStateL R)
      gelf_sched_to_target gelf_sched_to_source).
    - intros sR tR tL Ht. unfold gelf_sched_to_target. rewrite (isj_nat_input _ _ Ht).
      exact (svc_ps_state_rel_canonical Job PStateR PStateL R _).
    - intros sL tR tL Ht. destruct Ht.
      exact (svc_ps_state_rel_surjective Job PStateR PStateL R _).
  Qed.

  Lemma gelf_elf_rel (x y : Job) :
    ArBoolRel (@prosa.model.priority.definitions.hep_job Job ER x y)
      (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ EL x y).
  Proof. exact (ELF_correspondence Job Task ppR ppL Hpp jaR jaL Hja jtR jtL Hjt fpR fpL Hfp x y). Qed.

  Lemma gelf_gel_rel (x y : Job) :
    ArBoolRel (@prosa.model.priority.definitions.hep_job Job GR x y)
      (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ GL x y).
  Proof. exact (GEL_correspondence Job Task ppR ppL Hpp jaR jaL Hja jtR jtL Hjt x y). Qed.

  Lemma gelf_ep_task_related (x y : Task) :
    ArBoolRel (@prosa.model.priority.definitions.ep_task Task fpR x y)
      (I.Prosa_Model_Priority_Definitions_ep_task Task dT fpL x y).
  Proof.
    unfold prosa.model.priority.definitions.ep_task. cbn [I.Prosa_Model_Priority_Definitions_ep_task].
    exact (pd_bool_and_related _ _ _ _ (Hfp x y) (Hfp y x)).
  Qed.

  Lemma gelf_same_task_related (x y : Job) :
    ArBoolRel (@prosa.model.task.concept.same_task Job Task jtR x y)
      (I.Prosa_Model_Task_Concept_same_task Job dJ Task dT jtL x y).
  Proof.
    unfold prosa.model.task.concept.same_task. cbn [I.Prosa_Model_Task_Concept_same_task].
    exact (pd_eq_observation_transport Task _ _ _ _ (Hjt x) (Hjt y)).
  Qed.

  Section Sched.
    Variable sR : SchedR.
    Variable sL : SchedL.
    Hypothesis Hs : SvcScheduleRel Job PStateR PStateL R sR sL.
    Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
    Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
    Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

    Let Hsa := pp_scheduled_at_related Job PStateR PStateL R sR sL Hs.

    Lemma gelf_respects_elf_rel :
      PropSPropRel (@PDS.respects_JLFP_policy_at_preemption_point Job jaR costR PStateR jpR jrR arrR sR ER)
        (I.Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point
          Job dJ jaL costL PStateL jpL jrL arrL sL EL).
    Proof.
      exact (respects_JLFP_policy_at_preemption_point_correspondence Job jaR jaL costR costL PStateR PStateL R
        jpR jpL Hjp jrR jrL Hjr arrR arrL Harr sR sL Hs ER EL gelf_elf_rel).
    Qed.

    Lemma gelf_respects_gel_rel :
      PropSPropRel (@PDS.respects_JLFP_policy_at_preemption_point Job jaR costR PStateR jpR jrR arrR sR GR)
        (I.Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point
          Job dJ jaL costL PStateL jpL jrL arrL sL GL).
    Proof.
      exact (respects_JLFP_policy_at_preemption_point_correspondence Job jaR jaL costR costL PStateR PStateL R
        jpR jpL Hjp jrR jrL Hjr arrR arrL Harr sR sL Hs GR GL gelf_gel_rel).
    Qed.

    Lemma gelf_respects_fp_rel :
      PropSPropRel (@PDS.respects_FP_policy_at_preemption_point Task Job jtR jaR costR PStateR jpR jrR arrR sR fpR)
        (I.Prosa_Model_Schedule_PriorityDriven_respects_FP_policy_at_preemption_point
          Task dT Job dJ jtL jaL costL PStateL jpL jrL arrL sL fpL).
    Proof.
      exact (respects_FP_policy_at_preemption_point_correspondence Job jaR jaL costR costL PStateR PStateL R
        jpR jpL Hjp jrR jrL Hjr arrR arrL Harr sR sL Hs Task jtR jtL Hjt fpR fpL Hfp).
    Qed.

    Lemma gelf_valid_schedule_rel :
      PropSPropRel (@prosa.behavior.ready.valid_schedule Job jaR PStateR sR costR jrR arrR)
        (I.Prosa_Behavior_Ready_valid_schedule Job dJ jaL PStateL sL costL jrL arrL).
    Proof.
      unfold prosa.behavior.ready.valid_schedule, prosa.behavior.ready.jobs_must_be_ready_to_execute,
        prosa.behavior.ready.jobs_come_from_arrival_sequence.
      cbn [I.Prosa_Behavior_Ready_valid_schedule I.Prosa_Behavior_Ready_jobs_must_be_ready_to_execute
        I.Prosa_Behavior_Ready_jobs_come_from_arrival_sequence].
      apply ar_and_correspondence.
      - apply ar_forall_identity_correspondence. intro j.
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hsa j _ _ Ht))|].
        exact (arrives_in_correspondence_certificate Job arrR arrL j Harr).
      - apply ar_forall_identity_correspondence. intro j.
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hsa j _ _ Ht))|].
        exact (ar_bool_truth_correspondence _ _ (Hjr sR sL Hs j tR tL Ht)).
    Qed.

    Lemma gelf_sequential_tasks_rel :
      PropSPropRel (@prosa.model.task.sequentiality.sequential_tasks Job Task jtR jaR costR PStateR arrR sR)
        (I.Prosa_Model_Task_Sequentiality_sequential_tasks Job dJ Task dT jtL jaL costL PStateL arrL sL).
    Proof.
      unfold prosa.model.task.sequentiality.sequential_tasks.
      cbn [I.Prosa_Model_Task_Sequentiality_sequential_tasks].
      apply ar_forall_identity_correspondence. intro j1.
      apply ar_forall_identity_correspondence. intro j2.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j1 Harr)|].
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j2 Harr)|].
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (gelf_same_task_related j1 j2))|].
      apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ (Hja j1) (Hja j2))|].
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hsa j2 _ _ Ht))|].
      exact (ar_bool_truth_correspondence _ _
        (pp_completed_by_related Job costR costL Hcost PStateR PStateL R sR sL Hs j1 tR tL Ht)).
    Qed.
  End Sched.

  (** *** elf_generalizes_gel *)

  Definition src_elf_generalizes_gel : Prop :=
    ltac:(body_of (fun s : S.statement_elf_generalizes_gel => s Task ppR Job jtR PStateR jaR costR jpR jrR fpR)).
  Definition tgt_elf_generalizes_gel : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_Generality_Elf_elf_generalizes_gel
      Task dT Job dJ ppL jtL PStateL jaL costL jpL jrL fpL)).

  Theorem elf_generalizes_gel_correspondence : PropSPropRel src_elf_generalizes_gel tgt_elf_generalizes_gel.
  Proof.
    unfold src_elf_generalizes_gel, tgt_elf_generalizes_gel.
    apply ar_imp_correspondence.
    - apply ar_forall_identity_correspondence. intro tsk1.
      apply ar_forall_identity_correspondence. intro tsk2.
      exact (ar_bool_truth_correspondence _ _ (gelf_ep_task_related tsk1 tsk2)).
    - apply gelf_forall_sched. intros sR sL Hs.
      apply fpre_forall_arr. intros arrR arrL Harr.
      exact (gelf_iff_correspondence _ _ _ _ (gelf_respects_elf_rel sR sL Hs arrR arrL Harr)
        (gelf_respects_gel_rel sR sL Hs arrR arrL Harr)).
  Qed.

  (** *** elf_is_fixed_priority *)

  Definition src_elf_is_fixed_priority : Prop :=
    ltac:(body_of (fun s : S.statement_elf_is_fixed_priority => s Task ppR Job jtR PStateR jaR costR jpR jrR fpR)).
  Definition tgt_elf_is_fixed_priority : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_Generality_Elf_elf_is_fixed_priority
      Task dT Job dJ ppL jtL PStateL jaL costL jpL jrL fpL)).

  Theorem elf_is_fixed_priority_correspondence : PropSPropRel src_elf_is_fixed_priority tgt_elf_is_fixed_priority.
  Proof.
    unfold src_elf_is_fixed_priority, tgt_elf_is_fixed_priority.
    apply gelf_forall_sched. intros sR sL Hs.
    apply fpre_forall_arr. intros arrR arrL Harr.
    apply ar_imp_correspondence; [exact (gelf_respects_elf_rel sR sL Hs arrR arrL Harr)|].
    exact (gelf_respects_fp_rel sR sL Hs arrR arrL Harr).
  Qed.

  (** *** elf_generalizes_fixed_priority *)

  Definition src_elf_generalizes_fixed_priority : Prop :=
    ltac:(body_of (fun s : S.statement_elf_generalizes_fixed_priority =>
      s Task ppR Job jtR PStateR jaR costR jpR jrR fpR)).
  Definition tgt_elf_generalizes_fixed_priority : SProp :=
    ltac:(type_of_term (@I.Prosa_Results_Generality_Elf_elf_generalizes_fixed_priority
      Task dT Job dJ ppL jtL PStateL jaL costL jpL jrL fpL)).

  Theorem elf_generalizes_fixed_priority_correspondence :
    PropSPropRel src_elf_generalizes_fixed_priority tgt_elf_generalizes_fixed_priority.
  Proof.
    unfold src_elf_generalizes_fixed_priority, tgt_elf_generalizes_fixed_priority.
    apply ar_imp_correspondence.
    - apply ar_forall_identity_correspondence. intro tsk1.
      apply ar_forall_identity_correspondence. intro tsk2.
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (pd_ne_observation Task tsk1 tsk2))|].
      exact (ar_bool_truth_correspondence _ _ (pd_bool_not_related _ _ (gelf_ep_task_related tsk1 tsk2))).
    - apply fpre_forall_arr. intros arrR arrL Harr.
      apply gelf_forall_sched. intros sR sL Hs.
      apply ar_imp_correspondence; [exact (gelf_valid_schedule_rel sR sL Hs arrR arrL Harr)|].
      apply ar_imp_correspondence; [exact (gelf_sequential_tasks_rel sR sL Hs arrR arrL Harr)|].
      exact (gelf_iff_correspondence _ _ _ _ (gelf_respects_elf_rel sR sL Hs arrR arrL Harr)
        (gelf_respects_fp_rel sR sL Hs arrR arrL Harr)).
  Qed.

End Generality.
