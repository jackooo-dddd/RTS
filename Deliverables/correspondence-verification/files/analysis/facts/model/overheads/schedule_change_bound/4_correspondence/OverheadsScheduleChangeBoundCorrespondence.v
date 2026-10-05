From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import ScheduleChangeBoundSemanticSource.
From prosa Require Import behavior.all model.processor.overheads model.readiness.basic model.task.arrival.curves
  analysis.definitions.overheads.schedule_change.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedOverheadsScheduleChangeBound ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  OvhArrivalsSeqBaseAdapter OvhArrivalsSeqOperations OvhArrivalsSeqCorrespondence OvhArrivalsCorrespondence
  OvhJitterSvcBaseAdapter OvhJitterSvcNatBoolOperations OvhJitterSvcIntervalOperations
  OvhJitterSvcScheduleOperations OvhJitterSvcJobOperations OvhPreemptionParameterCorrespondence
  OvhPreemptionTimeCorrespondence OvhPriorityDrivenCorrespondence OvhPStateCoverHelpers OvhFactsPreemptionHelpers
  OvhWorkloadCorrespondence OvhPriorityInversionCorrespondence OvhExistenceHelpers OvhHepAtPtHelpers
  OvhTaskPreemptionParametersCorrespondence OvhBusyIntervalPiHelpers OvhStateRel OvhCurvesCorrespondence.
From FoundationCertificates Require ScheduleChangeStateAdapter ScheduleChangeCorrespondence.

Module I := ImportedOverheadsScheduleChangeBound.
Module S := ScheduleChangeBoundSemanticSource.ScheduleChangeBoundSemanticSource.
Module PP := PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.
Module SCS := ScheduleChangeStateAdapter.
Module SCC := ScheduleChangeCorrespondence.

(** Statement correspondences for [analysis/facts/model/overheads/schedule_change_bound.v].

    Source side: the extracted statements specialised at their leading input binders; target side: the imported
    Lean theorem types.  The overheads processor model is fixed on both sides and related by [ovh_psrel]
    (OvhStateRel.v, as in the accepted overheads-schedule certificate); the generic chain helpers are replayed at
    its universe instance (Ovh*.v, see their headers).  Covered in both directions: job-arrival, job-cost and
    preemption instances, JLFP policies, arrival sequences and schedules (as in the accepted overheads
    priority-bump certificate), job-task maps, task sets (the accepted list relation) and, where a statement
    quantifies over them inside, task types with their DecidableEq, MaxArrivals and JobTask instances (through
    Lean's funext, exported with its proof, as in the accepted FIFO facts certificate).  The FP statement's task
    type, arrival curves and FP policy are leading inputs related by the accepted relations (two-way totals).  The
    basic readiness model is fixed on both sides and related pointwise through [pending].  Schedules related by
    [ovh_psrel] are also related by the accepted schedule-change relation (constructor-wise), which gives the
    accepted [number_schedule_changes] certificate.  Jobs by identity, instants and durations by [SubNatRel].
    No source or target theorem is used. *)

Local Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Local Ltac type_of_term t := let T := type of t in exact T.

(** ** Task types quantified inside a statement *)

Section TypeCover.
  Variable T : I.Prosa_Model_Task_Concept_TaskType.
  Variable dT : I.DecidableEq T.

  Definition scb_eqb (x y : T) : bool :=
    match dT x y with
    | I.Decidable_isTrue _ => true
    | I.Decidable_isFalse _ => false
    end.

  Lemma scb_eqP : Equality.axiom scb_eqb.
  Proof.
    intros x y. unfold scb_eqb.
    destruct (dT x y) as [h|h].
    - apply ReflectF. intro E. exact (match h (coq_eq_to_imported_eq x y E) with end).
    - apply ReflectT. exact (imported_eq_to_coq_eq x y h).
  Qed.

  Definition scb_type_eqType : eqType := HB.pack T (hasDecEq.Build T scb_eqP).

  Lemma scb_decidable_unique (P : SProp) (d1 d2 : I.Decidable P) : Lean.eq d1 d2.
  Proof.
    destruct d1 as [h1|h1], d2 as [h2|h2].
    - exact (@Lean.eq_refl _ _).
    - destruct (h1 h2).
    - destruct (h2 h1).
    - exact (@Lean.eq_refl _ _).
  Qed.

  Lemma scb_decidable_eq : Lean.eq (ar_decidable_eq scb_type_eqType) dT.
  Proof.
    apply (I.Prosa_Validation_ScheduleChangeBoundInterface_production_funext T
      (fun a => forall b : T, I.Decidable (Lean.eq a b))).
    intro a.
    apply (I.Prosa_Validation_ScheduleChangeBoundInterface_production_funext T
      (fun b => I.Decidable (Lean.eq a b))).
    intro b. exact (scb_decidable_unique _ _ _).
  Qed.
End TypeCover.

Lemma scb_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall xsR xsL, ArListRel xsR xsL -> PropSPropRel (PR xsR) (PL xsL)) ->
  PropSPropRel (forall xs, PR xs) (forall xs, PL xs).
Proof.
  apply (isj_forall_cover_sprop _ _ ArListRel ar_list_to_imported ar_list_to_rocq).
  - intro xs. exact (@Lean.eq_refl _ _).
  - intro xs. exact (ar_list_target_roundtrip xs).
Qed.

Lemma scb_sum_filter_related (T : Type) (PR : T -> bool) (PL : T -> I.Bool)
    (FR : T -> nat) (FL : T -> Lean.Nat) xsR xsL :
  ArPredRel PR PL -> (forall x, SubNatRel (FR x) (FL x)) -> ArListRel xsR xsL ->
  SubNatRel (\sum_(x <- xsR | PR x) FR x) (ari_list_sum T FL (ar_target_filter PL xsL)).
Proof.
  intros HP HF Hxs. rewrite -big_filter.
  exact (ari_sum_related T FR FL _ _ HF (ar_filter_related T PR PL xsR xsL HP Hxs)).
Qed.

(** FP policies: pointwise on Booleans, with two-way totals. *)
Definition ScbFPRel (Task : eqType) (pR : prosa.model.priority.definitions.FP_policy Task)
    (pL : I.Prosa_Model_Priority_Definitions_FP_policy Task (ar_decidable_eq Task)) : SProp :=
  forall x y : Task,
    ArBoolRel (@prosa.model.priority.definitions.hep_task Task pR x y)
      (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task (ar_decidable_eq Task) pL x y).

Lemma scb_FP_policy_source_total (Task : eqType) pR :
  ScbFPRel Task pR
    (I.Prosa_Model_Priority_Definitions_FP_policy_mk Task (ar_decidable_eq Task)
      (fun x y => ar_bool_to_imported (@prosa.model.priority.definitions.hep_task Task pR x y))).
Proof. intros x y. exact (@Lean.eq_refl _ _). Qed.

Lemma scb_FP_policy_target_total (Task : eqType) pL :
  ScbFPRel Task
    (fun x y => ar_bool_to_rocq
      (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task (ar_decidable_eq Task) pL x y)) pL.
Proof. intros x y. exact (ar_bool_target_roundtrip _). Qed.

Section Stmts.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Let PR := prosa.model.processor.overheads.processor_state Job.
  Let PL := I.Prosa_Model_Processor_Overheads_processor_state Job dJ.
  Let X := ovh_psrel Job.

  Local Ltac imp H := apply ar_imp_correspondence; [exact H|].

  Lemma scb_forall_ja (P : prosa.behavior.job.JobArrival Job -> Prop)
      (Q : I.Prosa_Behavior_Job_JobArrival Job dJ -> SProp) :
    (forall a b, ArJobArrivalRel Job a b -> PropSPropRel (P a) (Q b)) ->
    PropSPropRel (forall a, P a) (forall b, Q b).
  Proof.
    exact (isj_forall_cover_sprop _ _ (ArJobArrivalRel Job) (ar_import_job_arrival Job)
      (svc_export_job_arrival Job) (ar_job_arrival_import_certificate Job) (svc_job_arrival_export Job) P Q).
  Qed.

  Lemma scb_forall_cost (P : prosa.behavior.job.JobCost Job -> Prop)
      (Q : I.Prosa_Behavior_Job_JobCost Job dJ -> SProp) :
    (forall a b, SvcJobCostRel Job a b -> PropSPropRel (P a) (Q b)) ->
    PropSPropRel (forall a, P a) (forall b, Q b).
  Proof.
    exact (isj_forall_cover_sprop _ _ (SvcJobCostRel Job) (svc_import_job_cost Job)
      (svc_export_job_cost Job) (svc_job_cost_import Job) (svc_job_cost_export Job) P Q).
  Qed.

  Definition ScbJobTaskRel (Task : eqType) (jtR : prosa.model.task.concept.JobTask Job Task)
      (jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task (ar_decidable_eq Task)) : SProp :=
    forall j : Job, Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task (ar_decidable_eq Task) jtL j).

  Lemma scb_forall_jt (Task : eqType) (P : prosa.model.task.concept.JobTask Job Task -> Prop)
      (Q : I.Prosa_Model_Task_Concept_JobTask Job dJ Task (ar_decidable_eq Task) -> SProp) :
    (forall a b, ScbJobTaskRel Task a b -> PropSPropRel (P a) (Q b)) ->
    PropSPropRel (forall a, P a) (forall b, Q b).
  Proof.
    apply (isj_forall_cover_sprop _ _ (ScbJobTaskRel Task)
      (fun jtR => I.Prosa_Model_Task_Concept_JobTask_mk Job dJ Task (ar_decidable_eq Task)
        (fun j => @prosa.model.task.concept.job_task Job Task jtR j))
      (fun jtL => ((fun j => I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task (ar_decidable_eq Task) jtL j)
        : prosa.model.task.concept.JobTask Job Task))).
    - intros jtR j. exact (@Lean.eq_refl _ _).
    - intros jtL j. exact (@Lean.eq_refl _ _).
  Qed.

  (** Task types (with their DecidableEq, MaxArrivals and JobTask instances) quantified inside a statement. *)
  Lemma scb_forall_task
      (PRt : forall Task : eqType, prosa.model.task.arrival.curves.MaxArrivals Task ->
        prosa.model.task.concept.JobTask Job Task -> Prop)
      (PLt : forall (T : I.Prosa_Model_Task_Concept_TaskType) (dT : I.DecidableEq T),
        I.Prosa_Model_Task_Arrival_Curves_MaxArrivals T dT ->
        I.Prosa_Model_Task_Concept_JobTask Job dJ T dT -> SProp) :
    (forall (TR : eqType) (maR : prosa.model.task.arrival.curves.MaxArrivals TR)
        (maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals TR (ar_decidable_eq TR))
        (jtR : prosa.model.task.concept.JobTask Job TR)
        (jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ TR (ar_decidable_eq TR)),
        CvMaxArrivalsRel TR maR maL -> ScbJobTaskRel TR jtR jtL ->
        PropSPropRel (PRt TR maR jtR) (PLt TR (ar_decidable_eq TR) maL jtL)) ->
    PropSPropRel (forall TR maR jtR, PRt TR maR jtR) (forall T dT maL jtL, PLt T dT maL jtL).
  Proof.
    intro H. apply prop_sprop_rel_intro.
    - intros HR T dT.
      refine (isj_lean_transport
        (fun d => forall (maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals T d)
          (jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ T d), PLt T d maL jtL)
        _ _ (scb_decidable_eq T dT) _).
      intros maL jtL.
      pose E := scb_type_eqType T dT.
      pose maR := ((fun tsk => cv_export_fun
          (I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals E (ar_decidable_eq E) maL tsk))
        : prosa.model.task.arrival.curves.MaxArrivals E).
      pose jtR := ((fun j => I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ E (ar_decidable_eq E) jtL j)
        : prosa.model.task.concept.JobTask Job E).
      exact (prop_to_sprop _ _ (H E maR maL jtR jtL (MaxArrivals_target_total E maL) (fun j => @Lean.eq_refl _ _))
        (HR E maR jtR)).
    - intro HL. apply strictly_inhabits. intros TR maR jtR.
      pose maL := I.Prosa_Model_Task_Arrival_Curves_MaxArrivals_mk TR (ar_decidable_eq TR)
        (fun tsk => cv_import_fun (@prosa.model.task.arrival.curves.max_arrivals TR maR tsk)).
      pose jtL := I.Prosa_Model_Task_Concept_JobTask_mk Job dJ TR (ar_decidable_eq TR)
        (fun j => @prosa.model.task.concept.job_task Job TR jtR j).
      exact (sprop_to_prop _ _ (H TR maR maL jtR jtL (MaxArrivals_source_total TR maR) (fun j => @Lean.eq_refl _ _))
        (HL TR (ar_decidable_eq TR) maL jtL)).
  Qed.

  Lemma scb_sc_sched sR sL (Hs : IsjPSchedRel Job PR PL X sR sL) : SCS.ScScheduleRel Job sR sL.
  Proof.
    intros tR tL Ht.
    refine (sub_imported_eq_trans _ _ _ _ (Hs tR tL Ht)). cbn.
    destruct (sR tR) as [| a b | a | j | j]; cbn; try destruct a; try destruct b; exact (@Lean.eq_refl _ _).
  Qed.

  Lemma scb_count_related sR sL (Hs : IsjPSchedRel Job PR PL X sR sL) t1R t1L dR dL :
    SubNatRel t1R t1L -> SubNatRel dR dL ->
    SubNatRel (@prosa.analysis.definitions.overheads.schedule_change.number_schedule_changes Job sR t1R.+1 (t1R + dR))
      (I.Prosa_Analysis_Definitions_Overheads_ScheduleChange_number_schedule_changes Job dJ sL
        (sub_imported_add t1L (sub_nat_to_imported 1)) (sub_imported_add t1L dL)).
  Proof.
    intros H1 Hd.
    exact (SCC.number_schedule_changes_correspondence Job sR sL (scb_sc_sched sR sL Hs) _ _ _ _
      (pp_succ_related _ _ H1) (sub_add_correspondence _ _ _ _ H1 Hd)).
  Qed.

  Section Instances.
    Variable jaR : prosa.behavior.job.JobArrival Job.
    Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
    Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
    Variable costR : prosa.behavior.job.JobCost Job.
    Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
    Hypothesis Hcost : SvcJobCostRel Job costR costL.

    Section Pair.
      Variable sR : @prosa.behavior.schedule.schedule Job PR.
      Variable sL : I.Prosa_Behavior_Schedule_schedule_inst4 Job dJ PL.
      Hypothesis Hs : IsjPSchedRel Job PR PL X sR sL.

      Let Hsa := isj_psr_scheduled_at_related Job PR PL X sR sL Hs.
      Let COMPLETED := fpre_completed_by_related Job costR costL Hcost PR PL X sR sL Hs.

      Lemma scb_basic_ready_rel :
        FpreJrAt Job jaR jaL costR costL PR PL sR sL
          (@prosa.model.readiness.basic.basic_ready_instance Job PR jaR costR)
          (I.Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job dJ PL jaL costL).
      Proof.
        intros j tR tL Ht.
        exact (fpre_pending_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs j tR tL Ht).
      Qed.

      Lemma scb_preempted_at_related (j : Job) tR tL (Ht : SubNatRel tR tL) :
        ArBoolRel (@PP.preempted_at Job costR PR sR j tR)
          (I.Prosa_Model_Preemption_Parameter_preempted_at_inst4 Job dJ costL PL sL j tL).
      Proof.
        unfold PP.preempted_at.
        cbn [I.Prosa_Model_Preemption_Parameter_preempted_at_inst4].
        rewrite -subn1.
        apply ar_bool_and_related; [apply ar_bool_and_related|].
        - exact (Hsa j _ _ (svc_target_sub_related _ _ _ _ Ht (sub_nat_rel_canonical 1))).
        - exact (svc_bool_not_related _ _ (COMPLETED j tR tL Ht)).
        - exact (svc_bool_not_related _ _ (Hsa j tR tL Ht)).
      Qed.

      Lemma scb_no_superfluous_rel pR pL (Hp : FpreJLFPRel Job pR pL) :
        PropSPropRel
          (@PP.no_superfluous_preemptions Job costR
            (@prosa.model.priority.coercion.JLFP_to_JLDP Job pR) PR sR)
          (I.Prosa_Model_Preemption_Parameter_no_superfluous_preemptions_inst4 Job dJ costL
            (I.Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job dJ pL) PL sL).
      Proof.
        unfold PP.no_superfluous_preemptions.
        cbn [I.Prosa_Model_Preemption_Parameter_no_superfluous_preemptions_inst4].
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_forall_identity_correspondence. intro j.
        apply ar_forall_identity_correspondence. intro jhp.
        apply ar_imp_correspondence;
          [exact (ar_bool_truth_correspondence _ _ (scb_preempted_at_related j tR tL Ht))|].
        apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hsa jhp tR tL Ht))|].
        exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (Hp j jhp))).
      Qed.
    End Pair.

    Lemma scb_all_jobs_from_taskset_related (Task : eqType) jtR jtL (Hjt : ScbJobTaskRel Task jtR jtL)
        arrR arrL (Harr : ArArrivalSequenceRel Job arrR arrL) tsR tsL :
      ArListRel tsR tsL ->
      PropSPropRel (@prosa.model.task.concept.all_jobs_from_taskset Task Job jtR arrR tsR)
        (I.Prosa_Model_Task_Concept_all_jobs_from_taskset Task (ar_decidable_eq Task) Job dJ jtL arrL tsL).
    Proof.
      intro Hts.
      unfold prosa.model.task.concept.all_jobs_from_taskset.
      cbn [I.Prosa_Model_Task_Concept_all_jobs_from_taskset].
      apply ar_forall_identity_correspondence => j.
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j Harr)|].
      rewrite -(imported_eq_to_coq_eq _ _ (Hjt j)).
      exact (ar_bool_truth_correspondence _ _ (ar_decide_mem_related Task _ _ _ Hts)).
    Qed.
  End Instances.

  Local Ltac prefix jaR jaL Hja costR costL Hcost arrR arrL Harr sR sL Hs pR pL Hp jpR jpL Hjp :=
    apply (fpre_forall_arr Job); intros arrR arrL Harr;
    imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr);
    apply (fpre_forall_sched Job PR PL X); intros sR sL Hs;
    imp (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr _ _
      (scb_basic_ready_rel jaR jaL Hja costR costL Hcost sR sL Hs));
    imp (ex_work_conserving_related Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr _ _
      (scb_basic_ready_rel jaR jaL Hja costR costL Hcost sR sL Hs));
    imp (scb_no_superfluous_rel costR costL Hcost sR sL Hs pR pL Hp).
  Local Ltac busy jaR jaL Hja costR costL Hcost arrR arrL Harr sR sL Hs pR pL Hp j t1R t1L H1 t2R t2L H2 :=
    apply ar_forall_identity_correspondence; intro j;
    imp (arrives_in_correspondence_certificate Job arrR arrL j Harr);
    imp (ar_bool_truth_correspondence _ _ (ex_job_cost_positive_related Job costR costL Hcost j));
    apply ar_forall_nat_correspondence; intros t1R t1L H1;
    apply ar_forall_nat_correspondence; intros t2R t2L H2;
    imp (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr
      pR pL Hp j t1R t1L t2R t2L H1 H2).

  Definition src_schedule_changes_bounded_by_total_arrivals_JLFP : Prop :=
    ltac:(body_of (fun s : S.statement_schedule_changes_bounded_by_total_arrivals_JLFP => s Job)).
  Definition tgt_schedule_changes_bounded_by_total_arrivals_JLFP : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Overheads_ScheduleChangeBound_schedule_changes_bounded_by_total_arrivals_JLFP Job dJ)).
  Theorem schedule_changes_bounded_by_total_arrivals_JLFP_correspondence :
    PropSPropRel src_schedule_changes_bounded_by_total_arrivals_JLFP tgt_schedule_changes_bounded_by_total_arrivals_JLFP.
  Proof.
    unfold src_schedule_changes_bounded_by_total_arrivals_JLFP, tgt_schedule_changes_bounded_by_total_arrivals_JLFP.
    apply scb_forall_ja; intros jaR jaL Hja.
    apply scb_forall_cost; intros costR costL Hcost.
    apply (fpre_forall_jp Job); intros jpR jpL Hjp.
    apply (fpre_forall_jlfp Job); intros pR pL Hp.
    imp (fpre_reflexive_rel Job pR pL Hp).
    imp (hap_transitive_rel Job pR pL Hp).
    prefix jaR jaL Hja costR costL Hcost arrR arrL Harr sR sL Hs pR pL Hp jpR jpL Hjp.
    imp (fpre_respects_jlfp_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr _ _
      (scb_basic_ready_rel jaR jaL Hja costR costL Hcost sR sL Hs) jpR jpL Hjp pR pL Hp).
    imp (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL Harr jpR jpL Hjp).
    busy jaR jaL Hja costR costL Hcost arrR arrL Harr sR sL Hs pR pL Hp j t1R t1L H1 t2R t2L H2.
    apply scb_forall_task. intros TR maR maL jtR jtL Hma Hjt.
    apply scb_forall_list. intros tsR tsL Hts.
    imp (scb_all_jobs_from_taskset_related TR jtR jtL Hjt arrR arrL Harr tsR tsL Hts).
    imp (taskset_respects_max_arrivals_correspondence TR Job jtR jtL Hjt arrR arrL Harr tsR tsL Hts maR maL Hma).
    apply ar_forall_nat_correspondence. intros dR dL Hd.
    imp (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ H1 Hd) H2).
    exact (sub_nat_le_correspondence _ _ _ _ (scb_count_related sR sL Hs _ _ _ _ H1 Hd)
      (sub_mul_correspondence _ _ _ _ (sub_nat_rel_canonical 2)
        (ari_sum_related TR _ _ _ _ (fun tsk => Hma tsk _ _ Hd) Hts))).
  Qed.

  Definition src_schedule_changes_bounded_by_total_arrivals_FIFO : Prop :=
    ltac:(body_of (fun s : S.statement_schedule_changes_bounded_by_total_arrivals_FIFO => s Job)).
  Definition tgt_schedule_changes_bounded_by_total_arrivals_FIFO : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Overheads_ScheduleChangeBound_schedule_changes_bounded_by_total_arrivals_FIFO Job dJ)).
  Theorem schedule_changes_bounded_by_total_arrivals_FIFO_correspondence :
    PropSPropRel src_schedule_changes_bounded_by_total_arrivals_FIFO tgt_schedule_changes_bounded_by_total_arrivals_FIFO.
  Proof.
    unfold src_schedule_changes_bounded_by_total_arrivals_FIFO, tgt_schedule_changes_bounded_by_total_arrivals_FIFO.
    apply scb_forall_ja; intros jaR jaL Hja.
    apply scb_forall_cost; intros costR costL Hcost.
    apply (fpre_forall_jp Job); intros jpR jpL Hjp.
    apply (fpre_forall_jlfp Job); intros pR pL Hp.
    apply ar_imp_correspondence.
    { unfold prosa.model.priority.definitions.policy_is_FIFO.
      cbn [I.Prosa_Model_Priority_Definitions_policy_is_FIFO].
      apply ar_forall_identity_correspondence. intro j1.
      apply ar_forall_identity_correspondence. intro j2.
      exact (ar_bool_eq_correspondence _ _ _ _ (Hp j1 j2) (ar_decide_le_related _ _ _ _ (Hja j1) (Hja j2))). }
    prefix jaR jaL Hja costR costL Hcost arrR arrL Harr sR sL Hs pR pL Hp jpR jpL Hjp.
    imp (fpre_respects_jlfp_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr _ _
      (scb_basic_ready_rel jaR jaL Hja costR costL Hcost sR sL Hs) jpR jpL Hjp pR pL Hp).
    imp (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL Harr jpR jpL Hjp).
    busy jaR jaL Hja costR costL Hcost arrR arrL Harr sR sL Hs pR pL Hp j t1R t1L H1 t2R t2L H2.
    apply scb_forall_task. intros TR maR maL jtR jtL Hma Hjt.
    apply scb_forall_list. intros tsR tsL Hts.
    imp (scb_all_jobs_from_taskset_related TR jtR jtL Hjt arrR arrL Harr tsR tsL Hts).
    imp (taskset_respects_max_arrivals_correspondence TR Job jtR jtL Hjt arrR arrL Harr tsR tsL Hts maR maL Hma).
    apply ar_forall_nat_correspondence. intros dR dL Hd.
    imp (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ H1 Hd) H2).
    exact (sub_nat_le_correspondence _ _ _ _ (scb_count_related sR sL Hs _ _ _ _ H1 Hd)
      (ari_sum_related TR _ _ _ _ (fun tsk => Hma tsk _ _ Hd) Hts)).
  Qed.

  Section FP.
    Context (Task : eqType).
    Let dT := ar_decidable_eq Task.
    Variable maR : prosa.model.task.arrival.curves.MaxArrivals Task.
    Variable maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT.
    Hypothesis Hma : CvMaxArrivalsRel Task maR maL.
    Variable fR : prosa.model.priority.definitions.FP_policy Task.
    Variable fL : I.Prosa_Model_Priority_Definitions_FP_policy Task dT.
    Hypothesis Hf : ScbFPRel Task fR fL.

    Section JT.
      Variable jtR : prosa.model.task.concept.JobTask Job Task.
      Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
      Hypothesis Hjt : ScbJobTaskRel Task jtR jtL.

      Lemma scb_fp_hep_job_related :
        FpreJLFPRel Job (@prosa.model.priority.coercion.FP_to_JLFP Job Task jtR fR)
          (I.Prosa_Model_Priority_Coercion_FP_to_JLFP Job dJ Task dT jtL fL).
      Proof.
        intros x y.
        change (ArBoolRel (@prosa.model.priority.definitions.hep_task Task fR
            (@prosa.model.task.concept.job_task Job Task jtR x) (@prosa.model.task.concept.job_task Job Task jtR y))
          (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fL
            (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL x)
            (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL y))).
        refine (ari_lean_transport (fun v => ArBoolRel _
          (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fL v
            (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL y))) _ _ (Hjt x) _).
        refine (ari_lean_transport (fun v => ArBoolRel _
          (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fL
            (@prosa.model.task.concept.job_task Job Task jtR x) v)) _ _ (Hjt y) _).
        exact (Hf _ _).
      Qed.

      Lemma scb_fp_task_pred (j : Job) :
        ArPredRel (fun tsk => @prosa.model.priority.definitions.hep_task Task fR tsk
              (@prosa.model.task.concept.job_task Job Task jtR j))
            (fun tsk => I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fL tsk
              (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j)).
      Proof.
        intro tsk.
        refine (ari_lean_transport (fun v => ArBoolRel _
          (I.Prosa_Model_Priority_Definitions_FP_policy_hep_task Task dT fL tsk v)) _ _ (Hjt j) _).
        exact (Hf _ _).
      Qed.
    End JT.

    Lemma scb_reflexive_task_rel :
      PropSPropRel (@prosa.model.priority.definitions.reflexive_task_priorities Task fR)
        (I.Prosa_Model_Priority_Definitions_reflexive_task_priorities Task dT fL).
    Proof.
      unfold prosa.model.priority.definitions.reflexive_task_priorities.
      cbn [I.Prosa_Model_Priority_Definitions_reflexive_task_priorities].
      apply ar_forall_identity_correspondence. intro tsk.
      exact (ar_bool_truth_correspondence _ _ (Hf tsk tsk)).
    Qed.

    Lemma scb_transitive_task_rel :
      PropSPropRel (@prosa.model.priority.definitions.transitive_task_priorities Task fR)
        (I.Prosa_Model_Priority_Definitions_transitive_task_priorities Task dT fL).
    Proof.
      unfold prosa.model.priority.definitions.transitive_task_priorities.
      cbn [I.Prosa_Model_Priority_Definitions_transitive_task_priorities].
      apply ar_forall_identity_correspondence. intro y.
      apply ar_forall_identity_correspondence. intro x.
      apply ar_forall_identity_correspondence. intro z.
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hf x y))|].
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hf y z))|].
      exact (ar_bool_truth_correspondence _ _ (Hf x z)).
    Qed.

    Definition src_schedule_changes_bounded_by_total_arrivals_FP : Prop :=
      ltac:(body_of (fun s : S.statement_schedule_changes_bounded_by_total_arrivals_FP => s Task maR fR Job)).
    Definition tgt_schedule_changes_bounded_by_total_arrivals_FP : SProp :=
      ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Overheads_ScheduleChangeBound_schedule_changes_bounded_by_total_arrivals_FP
        Task dT maL fL Job dJ)).
    Theorem schedule_changes_bounded_by_total_arrivals_FP_correspondence :
      PropSPropRel src_schedule_changes_bounded_by_total_arrivals_FP tgt_schedule_changes_bounded_by_total_arrivals_FP.
    Proof.
      unfold src_schedule_changes_bounded_by_total_arrivals_FP, tgt_schedule_changes_bounded_by_total_arrivals_FP.
      apply scb_forall_ja; intros jaR jaL Hja.
      apply (scb_forall_jt Task); intros jtR jtL Hjt.
      apply scb_forall_cost; intros costR costL Hcost.
      apply (fpre_forall_jp Job); intros jpR jpL Hjp.
      imp scb_reflexive_task_rel.
      imp scb_transitive_task_rel.
      pose proof (scb_fp_hep_job_related jtR jtL Hjt) as Hp.
      prefix jaR jaL Hja costR costL Hcost arrR arrL Harr sR sL Hs
        (@prosa.model.priority.coercion.FP_to_JLFP Job Task jtR fR)
        (I.Prosa_Model_Priority_Coercion_FP_to_JLFP Job dJ Task dT jtL fL) Hp jpR jpL Hjp.
      imp (fpre_respects_jlfp_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr _ _
        (scb_basic_ready_rel jaR jaL Hja costR costL Hcost sR sL Hs) jpR jpL Hjp _ _ Hp).
      imp (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL Harr jpR jpL Hjp).
      busy jaR jaL Hja costR costL Hcost arrR arrL Harr sR sL Hs
        (@prosa.model.priority.coercion.FP_to_JLFP Job Task jtR fR)
        (I.Prosa_Model_Priority_Coercion_FP_to_JLFP Job dJ Task dT jtL fL) Hp j t1R t1L H1 t2R t2L H2.
      apply scb_forall_list. intros tsR tsL Hts.
      imp (scb_all_jobs_from_taskset_related Task jtR jtL Hjt arrR arrL Harr tsR tsL Hts).
      imp (taskset_respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsR tsL Hts maR maL Hma).
      apply ar_forall_nat_correspondence. intros dR dL Hd.
      imp (sub_nat_le_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ H1 Hd) H2).
      exact (sub_nat_le_correspondence _ _ _ _ (scb_count_related sR sL Hs _ _ _ _ H1 Hd)
        (sub_mul_correspondence _ _ _ _ (sub_nat_rel_canonical 2)
          (scb_sum_filter_related Task _ _ _ _ _ _ (scb_fp_task_pred jtR jtL Hjt j) (fun tsk => Hma tsk _ _ Hd) Hts))).
    Qed.
  End FP.
End Stmts.
