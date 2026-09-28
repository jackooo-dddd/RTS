From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import FactsPriorityFifoSemanticSource.
From prosa Require Import behavior.all model.processor.platform_properties model.schedule.scheduled
  model.priority.classes model.task.sequentiality model.priority.fifo model.readiness.basic
  model.schedule.work_conserving model.schedule.nonpreemptive analysis.definitions.always_higher_priority
  model.job.properties.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsPriorityFifo ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers
  WorkloadCorrespondence PriorityInversionCorrespondence ExistenceHelpers HepAtPtHelpers
  TaskPreemptionParametersCorrespondence BusyIntervalPiHelpers ServiceInversionPredCorrespondence
  BsiHelpers PcoBaseAdapter PcoStaticOrder PcoDynamicOrder PriorityCoercionCorrespondence FifoHelpers.

Module I := ImportedFactsPriorityFifo.
Module S := FactsPriorityFifoSemanticSource.FactsPriorityFifoSemanticSource.
Module PP := PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.
Module PDS := PriorityDrivenSemanticSource.PriorityDrivenSemanticSource.
Module PIS := PriorityInversionSemanticSource.PriorityInversionSemanticSource.
Module SIB := ServiceInversionBusyPrefixSemanticSource.ServiceInversionBusyPrefixSemanticSource.
Module SIP := ServiceInversionPredSemanticSource.ServiceInversionPredSemanticSource.

(** Statement correspondences for [analysis/facts/priority/fifo.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs (the job type, the arrival and cost classes, and for
    [fifo_respects_sequential_tasks] the task type and job-task class);
    target side: the imported Lean theorem types.  Inputs: [job_arrival]
    pointwise, [job_cost] by the accepted [SvcJobCostRel], [job_task] by
    [Lean.eq].  Inputs quantified inside a statement are covered in both
    directions: arrival sequences ([fpre_forall_arr]), processor models (the
    accepted [isj_cover_pstate]), schedules through the processor-model
    relation ([fpre_forall_sched]), [JobPreemptable] instances
    ([fpre_forall_jp]), jobs, tasks and instants, and task types with their
    decidable equality and job-task class ([ffifo_forall_task]).

    Task types: a Rocq [eqType] is sent to its carrier with the canonical
    decision procedure; a Lean type with a [DecidableEq] instance is sent to
    the [eqType] built from that instance, whose canonical decision procedure
    equals the given one by Lean's function extensionality (exported with its
    proof from [Quot.sound], on the importer allowlist) and the uniqueness of
    Lean decision procedures (both [Decidable] alternatives carry SProp
    proofs).

    [FIFO] is the accepted FIFO certificate; the readiness instance
    [basic_ready_instance] is pendency, related pointwise at the statement's
    schedule pair by the accepted [fpre_pending_related]; schedule validity,
    preemption models, the JLFP policy at preemption points, work
    conservation, busy-interval prefixes, priority inversion and its bound
    are the accepted preemption-facts and busy-interval existence helpers;
    cumulative service inversion is the accepted service-inversion helper;
    [preempted_at], [no_superfluous_preemptions], [nonpreemptive_schedule],
    [always_higher_priority] and sequential tasks are related by unfolding
    over the scheduled/completion observations.  No source or target theorem
    is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

(** ** Task types quantified inside a statement *)

Section TypeCover.
  Variable T : I.Prosa_Model_Task_Concept_TaskType.
  Variable dT : I.DecidableEq T.

  Definition ffifo_eqb (x y : T) : bool :=
    match dT x y with
    | I.Decidable_isTrue _ => true
    | I.Decidable_isFalse _ => false
    end.

  Lemma ffifo_eqP : Equality.axiom ffifo_eqb.
  Proof.
    intros x y. unfold ffifo_eqb.
    destruct (dT x y) as [h|h].
    - apply ReflectF. intro E. exact (match h (coq_eq_to_imported_eq x y E) with end).
    - apply ReflectT. exact (imported_eq_to_coq_eq x y h).
  Qed.

  Definition ffifo_type_eqType : eqType := HB.pack T (hasDecEq.Build T ffifo_eqP).

  Lemma ffifo_decidable_unique (P : SProp) (d1 d2 : I.Decidable P) : Lean.eq d1 d2.
  Proof.
    destruct d1 as [h1|h1], d2 as [h2|h2].
    - exact (@Lean.eq_refl _ _).
    - destruct (h1 h2).
    - destruct (h2 h1).
    - exact (@Lean.eq_refl _ _).
  Qed.

  Lemma ffifo_decidable_eq : Lean.eq (ar_decidable_eq ffifo_type_eqType) dT.
  Proof.
    apply (I.Prosa_Validation_FactsPriorityFifoInterface_production_funext T
      (fun a => forall b : T, I.Decidable (Lean.eq a b))).
    intro a.
    apply (I.Prosa_Validation_FactsPriorityFifoInterface_production_funext T
      (fun b => I.Decidable (Lean.eq a b))).
    intro b. exact (ffifo_decidable_unique _ _ _).
  Qed.
End TypeCover.

Section Fifo.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.

  Lemma ffifo_forall_task
      (PR : forall Task : eqType, prosa.model.task.concept.JobTask Job Task -> Prop)
      (PL : forall (T : I.Prosa_Model_Task_Concept_TaskType) (dT : I.DecidableEq T),
        I.Prosa_Model_Task_Concept_JobTask Job dJ T dT -> SProp) :
    (forall (TR : eqType) (jtR : prosa.model.task.concept.JobTask Job TR)
        (jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ TR (ar_decidable_eq TR)),
        (forall j : Job, Lean.eq (@prosa.model.task.concept.job_task Job TR jtR j)
          (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ TR (ar_decidable_eq TR) jtL j)) ->
        PropSPropRel (PR TR jtR) (PL TR (ar_decidable_eq TR) jtL)) ->
    PropSPropRel (forall TR jtR, PR TR jtR) (forall T dT jtL, PL T dT jtL).
  Proof.
    intro H. apply prop_sprop_rel_intro.
    - intros HR T dT.
      refine (isj_lean_transport (fun d => forall jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ T d, PL T d jtL)
        _ _ (ffifo_decidable_eq T dT) _).
      intro jtL.
      pose E := ffifo_type_eqType T dT.
      pose jtR := ((fun j => I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ T (ar_decidable_eq E) jtL j)
        : prosa.model.task.concept.JobTask Job E).
      exact (prop_to_sprop _ _ (H E jtR jtL (fun j => @Lean.eq_refl _ _)) (HR E jtR)).
    - intro HL. apply strictly_inhabits. intros TR jtR.
      pose jtL := I.Prosa_Model_Task_Concept_JobTask_mk Job dJ TR (ar_decidable_eq TR)
        (fun j => @prosa.model.task.concept.job_task Job TR jtR j).
      exact (sprop_to_prop _ _ (H TR jtR jtL (fun j => @Lean.eq_refl _ _)) (HL TR (ar_decidable_eq TR) jtL)).
  Qed.

  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_arrival Job jaR j)
      (I.Prosa_Behavior_Job_JobArrival_job_arrival Job dJ jaL j).

  Let FR := @prosa.model.priority.fifo.FIFO Job jaR.
  Let FL := I.Prosa_Model_Priority_Fifo_FIFO Job dJ jaL.

  Lemma ffifo_hep_related (x y : Job) :
    ArBoolRel (@prosa.model.priority.definitions.hep_job Job FR x y)
      (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ FL x y).
  Proof. exact (FIFO_correspondence Job jaR jaL Hja x y). Qed.

  (** *** Statements about the policy *)

  Definition src_hep_job_arrival_FIFO : Prop :=
    ltac:(body_of (fun s : S.statement_hep_job_arrival_FIFO => s Job jaR)).
  Definition tgt_hep_job_arrival_FIFO : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Fifo_hep_job_arrival_FIFO Job dJ jaL)).

  Theorem hep_job_arrival_FIFO_correspondence : PropSPropRel src_hep_job_arrival_FIFO tgt_hep_job_arrival_FIFO.
  Proof.
    unfold src_hep_job_arrival_FIFO, tgt_hep_job_arrival_FIFO.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_identity_correspondence. intro j'.
    exact (ar_bool_eq_correspondence _ _ _ _ (ffifo_hep_related j j') (svc_decide_le_related _ _ _ _ (Hja j) (Hja j'))).
  Qed.

  Definition src_not_hep_job_arrival_FIFO : Prop :=
    ltac:(body_of (fun s : S.statement_not_hep_job_arrival_FIFO => s Job jaR)).
  Definition tgt_not_hep_job_arrival_FIFO : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Fifo_not_hep_job_arrival_FIFO Job dJ jaL)).

  Theorem not_hep_job_arrival_FIFO_correspondence :
    PropSPropRel src_not_hep_job_arrival_FIFO tgt_not_hep_job_arrival_FIFO.
  Proof.
    unfold src_not_hep_job_arrival_FIFO, tgt_not_hep_job_arrival_FIFO.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_identity_correspondence. intro j'.
    exact (ar_bool_eq_correspondence _ _ _ _ (svc_bool_not_related _ _ (ffifo_hep_related j j'))
      (svc_decide_lt_related _ _ _ _ (Hja j') (Hja j))).
  Qed.

  Definition src_not_hep_job_FIFO : Prop :=
    ltac:(body_of (fun s : S.statement_not_hep_job_FIFO => s Job jaR)).
  Definition tgt_not_hep_job_FIFO : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Fifo_not_hep_job_FIFO Job dJ jaL)).

  Theorem not_hep_job_FIFO_correspondence : PropSPropRel src_not_hep_job_FIFO tgt_not_hep_job_FIFO.
  Proof.
    unfold src_not_hep_job_FIFO, tgt_not_hep_job_FIFO.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_identity_correspondence. intro j'.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (ffifo_hep_related j j')))|].
    exact (ar_bool_truth_correspondence _ _ (ffifo_hep_related j' j)).
  Qed.

  Lemma ffifo_always_higher_priority_rel (x y : Job) :
    PropSPropRel (@prosa.analysis.definitions.always_higher_priority.always_higher_priority Job
        (@prosa.model.priority.coercion.JLFP_to_JLDP Job FR) x y)
      (I.Prosa_Analysis_Definitions_AlwaysHigherPriority_always_higher_priority Job dJ
        (I.Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job dJ FL) x y).
  Proof.
    unfold prosa.analysis.definitions.always_higher_priority.always_higher_priority.
    cbn [I.Prosa_Analysis_Definitions_AlwaysHigherPriority_always_higher_priority].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _ (ffifo_hep_related x y)
      (svc_bool_not_related _ _ (ffifo_hep_related y x)))).
  Qed.

  Definition src_not_hep_job_always_higher_priority_FIFO : Prop :=
    ltac:(body_of (fun s : S.statement_not_hep_job_always_higher_priority_FIFO => s Job jaR)).
  Definition tgt_not_hep_job_always_higher_priority_FIFO : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Fifo_not_hep_job_always_higher_priority_FIFO Job dJ jaL)).

  Theorem not_hep_job_always_higher_priority_FIFO_correspondence :
    PropSPropRel src_not_hep_job_always_higher_priority_FIFO tgt_not_hep_job_always_higher_priority_FIFO.
  Proof.
    unfold src_not_hep_job_always_higher_priority_FIFO, tgt_not_hep_job_always_higher_priority_FIFO.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_identity_correspondence. intro j'.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (ffifo_hep_related j j')))|].
    exact (ffifo_always_higher_priority_rel j' j).
  Qed.

  Definition src_fifo_respects_sequential_tasks (Task : eqType) (jtR : prosa.model.task.concept.JobTask Job Task) : Prop :=
    ltac:(body_of (fun s : S.statement_fifo_respects_sequential_tasks => s Job jaR Task jtR)).
  Definition tgt_fifo_respects_sequential_tasks (Task : eqType)
      (jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task (ar_decidable_eq Task)) : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Fifo_fifo_respects_sequential_tasks
      Job dJ jaL Task (ar_decidable_eq Task) jtL)).

  Theorem fifo_respects_sequential_tasks_correspondence (Task : eqType) jtR jtL
      (Hjt : forall j : Job, Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
        (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task (ar_decidable_eq Task) jtL j)) :
    PropSPropRel (src_fifo_respects_sequential_tasks Task jtR) (tgt_fifo_respects_sequential_tasks Task jtL).
  Proof.
    unfold src_fifo_respects_sequential_tasks, tgt_fifo_respects_sequential_tasks.
    unfold prosa.model.priority.definitions.policy_respects_sequential_tasks.
    cbn [I.Prosa_Model_Priority_Definitions_policy_respects_sequential_tasks].
    apply ar_forall_identity_correspondence. intro j1.
    apply ar_forall_identity_correspondence. intro j2.
    apply ar_imp_correspondence;
      [exact (ar_bool_truth_correspondence _ _ (pd_eq_observation_transport Task _ _ _ _ (Hjt j1) (Hjt j2)))|].
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ (Hja j1) (Hja j2))|].
    exact (ar_bool_truth_correspondence _ _ (ffifo_hep_related j1 j2)).
  Qed.

  (** *** Statements over a schedule *)

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

    Let Hsa := isj_psr_scheduled_at_related Job PR PL X sR sL Hs.
    Let COMPLETED := fpre_completed_by_related Job costR costL Hcost PR PL X sR sL Hs.

    Let BRR := @prosa.model.readiness.basic.basic_ready_instance Job PR jaR costR.
    Let BRL := I.Prosa_Model_Readiness_Basic_basic_ready_instance Job dJ PL jaL costL.

    Lemma ffifo_basic_ready_rel : FpreJrAt Job jaR jaL costR costL PR PL sR sL BRR BRL.
    Proof.
      intros j tR tL Ht.
      exact (fpre_pending_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs j tR tL Ht).
    Qed.

    Lemma ffifo_preempted_at_related (j : Job) tR tL (Ht : SubNatRel tR tL) :
      ArBoolRel (@PP.preempted_at Job costR PR sR j tR)
        (I.Prosa_Model_Preemption_Parameter_preempted_at Job dJ costL PL sL j tL).
    Proof.
      unfold PP.preempted_at. cbn [I.Prosa_Model_Preemption_Parameter_preempted_at].
      rewrite -subn1.
      apply ar_bool_and_related; [apply ar_bool_and_related|].
      - exact (Hsa j _ _ (svc_target_sub_related _ _ _ _ Ht (sub_nat_rel_canonical 1))).
      - exact (svc_bool_not_related _ _ (COMPLETED j tR tL Ht)).
      - exact (svc_bool_not_related _ _ (Hsa j tR tL Ht)).
    Qed.

    Lemma ffifo_no_superfluous_rel :
      PropSPropRel (@PP.no_superfluous_preemptions Job costR (@prosa.model.priority.coercion.JLFP_to_JLDP Job FR) PR sR)
        (I.Prosa_Model_Preemption_Parameter_no_superfluous_preemptions Job dJ costL
          (I.Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job dJ FL) PL sL).
    Proof.
      unfold PP.no_superfluous_preemptions.
      cbn [I.Prosa_Model_Preemption_Parameter_no_superfluous_preemptions].
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_identity_correspondence. intro jhp.
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _ (ffifo_preempted_at_related j tR tL Ht))|].
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hsa jhp tR tL Ht))|].
      exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (ffifo_hep_related j jhp))).
    Qed.

    Lemma ffifo_nonpreemptive_rel :
      PropSPropRel (@prosa.model.schedule.nonpreemptive.nonpreemptive_schedule Job costR PR sR)
        (I.Prosa_Model_Schedule_Nonpreemptive_nonpreemptive_schedule Job dJ costL PL sL).
    Proof.
      unfold prosa.model.schedule.nonpreemptive.nonpreemptive_schedule.
      cbn [I.Prosa_Model_Schedule_Nonpreemptive_nonpreemptive_schedule].
      apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros tR tL Ht.
      apply ar_forall_nat_correspondence. intros t'R t'L Ht'.
      apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Ht Ht')|].
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hsa j tR tL Ht))|].
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (COMPLETED j _ _ Ht')))|].
      exact (ar_bool_truth_correspondence _ _ (Hsa j _ _ Ht')).
    Qed.

    Section Arr.
      Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
      Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
      Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

      Lemma ffifo_sequential_tasks_rel (Task : eqType) jtR jtL
          (Hjt : forall j : Job, Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
            (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task (ar_decidable_eq Task) jtL j)) :
        PropSPropRel (@prosa.model.task.sequentiality.sequential_tasks Job Task jtR jaR costR PR arrR sR)
          (I.Prosa_Model_Task_Sequentiality_sequential_tasks Job dJ Task (ar_decidable_eq Task) jtL jaL costL PL arrL sL).
      Proof.
        unfold prosa.model.task.sequentiality.sequential_tasks.
        cbn [I.Prosa_Model_Task_Sequentiality_sequential_tasks].
        apply ar_forall_identity_correspondence. intro j1.
        apply ar_forall_identity_correspondence. intro j2.
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j1 Harr)|].
        apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j2 Harr)|].
        apply ar_imp_correspondence;
          [exact (ar_bool_truth_correspondence _ _ (pd_eq_observation_transport Task _ _ _ _ (Hjt j1) (Hjt j2)))|].
        apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ (Hja j1) (Hja j2))|].
        apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hsa j2 _ _ Ht))|].
        exact (ar_bool_truth_correspondence _ _ (COMPLETED j1 tR tL Ht)).
      Qed.
    End Arr.
  End Pair.

  (** The shared hypothesis prefix: a valid arrival sequence, a uniprocessor
      model, a schedule valid for the basic readiness model, a valid
      preemption model and the FIFO policy at preemption points. *)
  Local Ltac imp H := apply ar_imp_correspondence; [exact H|].
  Ltac ffifo_prefix arrR arrL Harr PR PL X sR sL Hs jpR jpL Hjp :=
    apply fpre_forall_arr; intros arrR arrL Harr;
    imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr);
    apply (isj_cover_pstate Job); intros PR PL X;
    imp (isj_psr_uniprocessor_related Job PR PL X);
    apply (fpre_forall_sched Job PR PL X); intros sR sL Hs;
    imp (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr _ _
      (ffifo_basic_ready_rel PR PL X sR sL Hs)).
  Ltac ffifo_pm arrR arrL Harr PR PL X sR sL Hs jpR jpL Hjp :=
    apply (fpre_forall_jp Job); intros jpR jpL Hjp;
    imp (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL Harr jpR jpL Hjp);
    imp (fpre_respects_jlfp_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr _ _
      (ffifo_basic_ready_rel PR PL X sR sL Hs) jpR jpL Hjp FR FL ffifo_hep_related).

  Definition src_FIFO_implies_no_priority_inversion : Prop :=
    ltac:(body_of (fun s : S.statement_FIFO_implies_no_priority_inversion => s Job jaR costR)).
  Definition tgt_FIFO_implies_no_priority_inversion : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Fifo_FIFO_implies_no_priority_inversion Job dJ jaL costL)).

  Theorem FIFO_implies_no_priority_inversion_correspondence :
    PropSPropRel src_FIFO_implies_no_priority_inversion tgt_FIFO_implies_no_priority_inversion.
  Proof.
    unfold src_FIFO_implies_no_priority_inversion, tgt_FIFO_implies_no_priority_inversion.
    ffifo_prefix arrR arrL Harr PR PL X sR sL Hs jpR jpL Hjp.
    ffifo_pm arrR arrL Harr PR PL X sR sL Hs jpR jpL Hjp.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    imp (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    imp (ar_bool_truth_correspondence _ _ (fpre_pending_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs j tR tL Ht)).
    exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _
      (ex_priority_inversion_related Job PR PL X sR sL Hs arrR arrL Harr FR FL ffifo_hep_related j tR tL Ht))).
  Qed.

  Definition src_scheduled_implies_higher_priority_completed : Prop :=
    ltac:(body_of (fun s : S.statement_scheduled_implies_higher_priority_completed => s Job jaR costR)).
  Definition tgt_scheduled_implies_higher_priority_completed : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Fifo_scheduled_implies_higher_priority_completed Job dJ jaL costL)).

  Theorem scheduled_implies_higher_priority_completed_correspondence :
    PropSPropRel src_scheduled_implies_higher_priority_completed tgt_scheduled_implies_higher_priority_completed.
  Proof.
    unfold src_scheduled_implies_higher_priority_completed, tgt_scheduled_implies_higher_priority_completed.
    ffifo_prefix arrR arrL Harr PR PL X sR sL Hs jpR jpL Hjp.
    ffifo_pm arrR arrL Harr PR PL X sR sL Hs jpR jpL Hjp.
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    imp (ar_bool_truth_correspondence _ _ (isj_psr_scheduled_at_related Job PR PL X sR sL Hs j tR tL Ht)).
    apply ar_forall_identity_correspondence. intro jhp.
    imp (arrives_in_correspondence_certificate Job arrR arrL jhp Harr).
    imp (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (ffifo_hep_related j jhp))).
    exact (ar_bool_truth_correspondence _ _ (fpre_completed_by_related Job costR costL Hcost PR PL X sR sL Hs jhp tR tL Ht)).
  Qed.

  Definition src_FIFO_implies_no_pi : Prop :=
    ltac:(body_of (fun s : S.statement_FIFO_implies_no_pi => s Job jaR costR)).
  Definition tgt_FIFO_implies_no_pi : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Fifo_FIFO_implies_no_pi Job dJ jaL costL)).

  Theorem FIFO_implies_no_pi_correspondence : PropSPropRel src_FIFO_implies_no_pi tgt_FIFO_implies_no_pi.
  Proof.
    unfold src_FIFO_implies_no_pi, tgt_FIFO_implies_no_pi.
    ffifo_prefix arrR arrL Harr PR PL X sR sL Hs jpR jpL Hjp.
    ffifo_pm arrR arrL Harr PR PL X sR sL Hs jpR jpL Hjp.
    apply ffifo_forall_task. intros Task jtR jtL Hjt.
    apply ar_forall_identity_correspondence. intro tsk.
    imp (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr _ _
      (ffifo_basic_ready_rel PR PL X sR sL Hs)).
    unfold PIS.priority_inversion_is_bounded_by.
    cbn [I.Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_is_bounded_by].
    apply ar_forall_identity_correspondence. intro j.
    imp (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    imp (ar_bool_truth_correspondence _ _ (pd_eq_observation_transport Task _ _ _ _ (Hjt j) (@Lean.eq_refl _ tsk))).
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (Hcost j)).
    exact (ex_pi_bounded_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr FR FL
      ffifo_hep_related j _ _ (fun nR nL Hn => sub_nat_rel_canonical O)).
  Qed.

  Definition src_FIFO_implies_no_service_inversion : Prop :=
    ltac:(body_of (fun s : S.statement_FIFO_implies_no_service_inversion => s Job jaR costR)).
  Definition tgt_FIFO_implies_no_service_inversion : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Fifo_FIFO_implies_no_service_inversion Job dJ jaL costL)).

  Theorem FIFO_implies_no_service_inversion_correspondence :
    PropSPropRel src_FIFO_implies_no_service_inversion tgt_FIFO_implies_no_service_inversion.
  Proof.
    unfold src_FIFO_implies_no_service_inversion, tgt_FIFO_implies_no_service_inversion.
    ffifo_prefix arrR arrL Harr PR PL X sR sL Hs jpR jpL Hjp.
    ffifo_pm arrR arrL Harr PR PL X sR sL Hs jpR jpL Hjp.
    apply ffifo_forall_task. intros Task jtR jtL Hjt.
    apply ar_forall_identity_correspondence. intro tsk.
    imp (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr _ _
      (ffifo_basic_ready_rel PR PL X sR sL Hs)).
    unfold SIB.service_inversion_is_bounded_by, SIP.pred_service_inversion_is_bounded_by,
      SIP.pred_service_inversion_of_job_is_bounded_by.
    cbn [I.Prosa_Analysis_Definitions_ServiceInversion_BusyPrefix_service_inversion_is_bounded_by
      I.Prosa_Analysis_Definitions_ServiceInversion_Pred_pred_service_inversion_is_bounded_by
      I.Prosa_Analysis_Definitions_ServiceInversion_Pred_pred_service_inversion_of_job_is_bounded_by].
    apply ar_forall_identity_correspondence. intro j.
    imp (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    imp (ar_bool_truth_correspondence _ _ (pd_eq_observation_transport Task _ _ _ _ (Hjt j) (@Lean.eq_refl _ tsk))).
    imp (sub_nat_lt_correspondence _ _ _ _ (sub_nat_rel_canonical O) (Hcost j)).
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
    imp (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs
      arrR arrL Harr FR FL ffifo_hep_related j _ _ _ _ Ht1 Ht2).
    exact (sub_nat_le_correspondence _ _ _ _
      (bsi_cumulative_service_inversion_related Job PR PL X sR sL Hs arrR arrL Harr
        _ _ (bsi_jlfp_to_jldp_rel Job FR FL ffifo_hep_related) j _ _ _ _ Ht1 Ht2)
      (sub_nat_rel_canonical O)).
  Qed.

  Definition src_tasks_execute_sequentially : Prop :=
    ltac:(body_of (fun s : S.statement_tasks_execute_sequentially => s Job jaR costR)).
  Definition tgt_tasks_execute_sequentially : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Fifo_tasks_execute_sequentially Job dJ jaL costL)).

  Theorem tasks_execute_sequentially_correspondence :
    PropSPropRel src_tasks_execute_sequentially tgt_tasks_execute_sequentially.
  Proof.
    unfold src_tasks_execute_sequentially, tgt_tasks_execute_sequentially.
    ffifo_prefix arrR arrL Harr PR PL X sR sL Hs jpR jpL Hjp.
    ffifo_pm arrR arrL Harr PR PL X sR sL Hs jpR jpL Hjp.
    apply ffifo_forall_task. intros Task jtR jtL Hjt.
    exact (ffifo_sequential_tasks_rel PR PL X sR sL Hs arrR arrL Harr Task jtR jtL Hjt).
  Qed.

  Ltac ffifo_wc arrR arrL Harr PR PL X sR sL Hs :=
    imp (ex_work_conserving_related Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr
      _ _ (ffifo_basic_ready_rel PR PL X sR sL Hs)).

  Definition src_no_preemptions_under_FIFO : Prop :=
    ltac:(body_of (fun s : S.statement_no_preemptions_under_FIFO => s Job jaR costR)).
  Definition tgt_no_preemptions_under_FIFO : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Fifo_no_preemptions_under_FIFO Job dJ jaL costL)).

  Theorem no_preemptions_under_FIFO_correspondence :
    PropSPropRel src_no_preemptions_under_FIFO tgt_no_preemptions_under_FIFO.
  Proof.
    unfold src_no_preemptions_under_FIFO, tgt_no_preemptions_under_FIFO.
    ffifo_prefix arrR arrL Harr PR PL X sR sL Hs jpR jpL Hjp.
    ffifo_wc arrR arrL Harr PR PL X sR sL Hs.
    ffifo_pm arrR arrL Harr PR PL X sR sL Hs jpR jpL Hjp.
    imp (ffifo_no_superfluous_rel PR PL X sR sL Hs).
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (ffifo_preempted_at_related PR PL X sR sL Hs j tR tL Ht))).
  Qed.

  Definition src_FIFO_is_nonpreemptive : Prop :=
    ltac:(body_of (fun s : S.statement_FIFO_is_nonpreemptive => s Job jaR costR)).
  Definition tgt_FIFO_is_nonpreemptive : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Priority_Fifo_FIFO_is_nonpreemptive Job dJ jaL costL)).

  Theorem FIFO_is_nonpreemptive_correspondence : PropSPropRel src_FIFO_is_nonpreemptive tgt_FIFO_is_nonpreemptive.
  Proof.
    unfold src_FIFO_is_nonpreemptive, tgt_FIFO_is_nonpreemptive.
    ffifo_prefix arrR arrL Harr PR PL X sR sL Hs jpR jpL Hjp.
    ffifo_wc arrR arrL Harr PR PL X sR sL Hs.
    ffifo_pm arrR arrL Harr PR PL X sR sL Hs jpR jpL Hjp.
    imp (ffifo_no_superfluous_rel PR PL X sR sL Hs).
    exact (ffifo_nonpreemptive_rel PR PL X sR sL Hs).
  Qed.

End Fifo.
