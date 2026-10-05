From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import OverheadsSbfFifoSemanticSource.
From prosa Require Import behavior.all model.processor.overheads model.processor.supply model.readiness.basic
  model.task.arrival.curves analysis.definitions.overheads.schedule_change GeneratedUnitGrowthSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedOverheadsSbfFifo ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  OvhArrivalsSeqBaseAdapter OvhArrivalsSeqOperations OvhArrivalsSeqCorrespondence OvhArrivalsCorrespondence
  OvhJitterSvcBaseAdapter OvhJitterSvcNatBoolOperations OvhJitterSvcIntervalOperations
  OvhJitterSvcScheduleOperations OvhJitterSvcJobOperations OvhPreemptionParameterCorrespondence
  OvhPreemptionTimeCorrespondence OvhPriorityDrivenCorrespondence OvhPStateCoverHelpers OvhFactsPreemptionHelpers
  OvhWorkloadCorrespondence OvhPriorityInversionCorrespondence OvhExistenceHelpers OvhHepAtPtHelpers
  OvhTaskPreemptionParametersCorrespondence OvhBusyIntervalPiHelpers OvhStateRel OvhCurvesCorrespondence.
From FoundationCertificates Require ScheduleChangeStateAdapter OverheadsBaseAdapter OverheadsCorrespondence
  OverheadResourceModelCorrespondence OsbfUnitGrowth.

Module I := ImportedOverheadsSbfFifo.
Module S := OverheadsSbfFifoSemanticSource.OverheadsSbfFifoSemanticSource.
Module PP := PreemptionParameterSemanticSource.PreemptionParameterSemanticSource.
Module SB := SbfBusySemanticSource.SbfBusySemanticSource.
Module OVC := OverheadsCorrespondence.
Module ORM := OverheadResourceModelCorrespondence.
Module UG := OsbfUnitGrowth.

(** Definition and statement correspondences for [analysis/facts/model/overheads/sbf/fifo.v].

    Source side: the extracted definitions and statements specialised at their leading input binders; target side:
    the compiled Lean definitions and the imported Lean theorem types.  The source's [SupplyBoundFunction] is a
    definitional class (a function of the interval length); the Lean class value is related through its field
    pointwise on Nat ([SubNatFunRel]).  [slowed] is the accepted generated validation source of util/unit_growth.v,
    related by the accepted unit-growth certificate (re-bound here).  The overheads processor model is fixed on
    both sides and related by [ovh_psrel] (OvhStateRel.v); the generic chain helpers are replayed at its universe
    instance (Ovh*.v, see their headers).  Leading inputs: the task type, its arrival curves (accepted relation with
    two-way totals) and, for the validity statement, the job type.  Covered in both directions: task sets (the
    accepted list relation), overhead bounds and interval lengths, job-task/job-arrival/job-cost/preemption
    instances, JLFP policies, arrival sequences and schedules; tasks and jobs by identity.  Schedules related by
    [ovh_psrel] are also related by the accepted constructor-wise overheads relation, which gives the accepted
    overhead-resource-model certificate.  The basic readiness model is fixed on both sides and related pointwise
    through [pending].  No source or target theorem is used. *)

Local Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Local Ltac type_of_term t := let T := type of t in exact T.

Lemma osf_forall_list (T : Type) (PR : seq T -> Prop) (PL : I.List T -> SProp) :
  (forall xsR xsL, ArListRel xsR xsL -> PropSPropRel (PR xsR) (PL xsL)) ->
  PropSPropRel (forall xs, PR xs) (forall xs, PL xs).
Proof.
  apply (isj_forall_cover_sprop _ _ ArListRel ar_list_to_imported ar_list_to_rocq).
  - intro xs. exact (@Lean.eq_refl _ _).
  - intro xs. exact (ar_list_target_roundtrip xs).
Qed.

(** Boolean conjunction in Prop position against a Lean conjunction of propositions. *)
Lemma osf_andb_and (a b : bool) (PL QL : SProp) :
  PropSPropRel (is_true a) PL -> PropSPropRel (is_true b) QL ->
  PropSPropRel (is_true (a && b)) (And PL QL).
Proof.
  intros Ha Hb. have Hab := ar_and_correspondence _ _ _ _ Ha Hb.
  apply prop_sprop_rel_intro.
  - intro H. exact (prop_to_sprop _ _ Hab (andP H)).
  - intro HL. apply strictly_inhabits. apply/andP. exact (sprop_to_prop _ _ Hab HL).
Qed.

(** Monotonicity (Boolean order) of related Nat functions. *)
Lemma osf_monotone_rel (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat) :
  SubNatFunRel fR fL ->
  PropSPropRel (prosa.util.rel.monotone leq fR)
    (I.Prosa_Util_Rel_monotone_inst1 Lean.Nat (fun x y => I.Decidable_decide (I.LE_le_inst1 Lean.Nat I.instLENat x y)
      (I.Nat_decLe x y)) fL).
Proof.
  intro Hf.
  unfold prosa.util.rel.monotone. cbn [I.Prosa_Util_Rel_monotone_inst1].
  apply ar_forall_nat_correspondence. intros xR xL Hx.
  apply ar_forall_nat_correspondence. intros yR yL Hy.
  apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (ar_decide_le_related _ _ _ _ Hx Hy))|].
  exact (ar_bool_truth_correspondence _ _ (ar_decide_le_related _ _ _ _ (Hf _ _ Hx) (Hf _ _ Hy))).
Qed.

Section Defs.
  Context (Task : eqType).
  Let dT := ar_decidable_eq Task.
  Variable maR : prosa.model.task.arrival.curves.MaxArrivals Task.
  Variable maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT.
  Hypothesis Hma : CvMaxArrivalsRel Task maR maL.

  Lemma fifo_blackout_bound_correspondence tsR tsL (Hts : ArListRel tsR tsL) DR DL CR CL PR PL
      (HD : SubNatRel DR DL) (HC : SubNatRel CR CL) (HP : SubNatRel PR PL) :
    SubNatFunRel (@S.fifo_blackout_bound Task maR tsR DR CR PR)
      (I.Prosa_Analysis_Facts_Model_Overheads_Sbf_Fifo_fifo_blackout_bound Task dT maL tsL DL CL PL).
  Proof.
    intros dR dL Hd. unfold S.fifo_blackout_bound.
    cbn [I.Prosa_Analysis_Facts_Model_Overheads_Sbf_Fifo_fifo_blackout_bound].
    exact (sub_mul_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ (sub_add_correspondence _ _ _ _ HD HC) HP)
      (sub_add_correspondence _ _ _ _ (sub_nat_rel_canonical 1)
        (ari_sum_related Task _ _ _ _ (fun tsk => Hma tsk _ _ Hd) Hts))).
  Qed.

  Lemma fifo_ovh_sbf_slow_correspondence tsR tsL (Hts : ArListRel tsR tsL) DR DL CR CL PR PL
      (HD : SubNatRel DR DL) (HC : SubNatRel CR CL) (HP : SubNatRel PR PL) :
    SubNatFunRel (@S.fifo_ovh_sbf_slow Task maR tsR DR CR PR)
      (I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function
        (I.Prosa_Analysis_Facts_Model_Overheads_Sbf_Fifo_fifo_ovh_sbf_slow Task dT maL tsL DL CL PL)).
  Proof.
    intros dR dL Hd. unfold S.fifo_ovh_sbf_slow.
    cbn [I.Prosa_Analysis_Facts_Model_Overheads_Sbf_Fifo_fifo_ovh_sbf_slow
      I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function].
    exact (UG.ug_sub_correspondence _ _ _ _ Hd
      (UG.ug_slowed_correspondence _ _ (fifo_blackout_bound_correspondence tsR tsL Hts DR DL CR CL PR PL HD HC HP)
        _ _ Hd)).
  Qed.

  Definition src_overheads_sbf_monotone : Prop :=
    ltac:(body_of (fun s : S.statement_overheads_sbf_monotone => s Task maR)).
  Definition tgt_overheads_sbf_monotone : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Overheads_Sbf_Fifo_overheads_sbf_monotone Task dT maL)).
  Theorem overheads_sbf_monotone_correspondence : PropSPropRel src_overheads_sbf_monotone tgt_overheads_sbf_monotone.
  Proof.
    unfold src_overheads_sbf_monotone, tgt_overheads_sbf_monotone.
    apply osf_forall_list. intros tsR tsL Hts.
    apply ar_forall_nat_correspondence. intros DR DL HD.
    apply ar_forall_nat_correspondence. intros CR CL HC.
    apply ar_forall_nat_correspondence. intros PR PL HP.
    exact (osf_monotone_rel _ _ (fifo_ovh_sbf_slow_correspondence tsR tsL Hts DR DL CR CL PR PL HD HC HP)).
  Qed.

  Definition src_fifo_blackout_bound_monotone : Prop :=
    ltac:(body_of (fun s : S.statement_fifo_blackout_bound_monotone => s Task maR)).
  Definition tgt_fifo_blackout_bound_monotone : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Overheads_Sbf_Fifo_fifo_blackout_bound_monotone Task dT maL)).
  Theorem fifo_blackout_bound_monotone_correspondence :
    PropSPropRel src_fifo_blackout_bound_monotone tgt_fifo_blackout_bound_monotone.
  Proof.
    unfold src_fifo_blackout_bound_monotone, tgt_fifo_blackout_bound_monotone.
    apply osf_forall_list. intros tsR tsL Hts.
    apply ar_imp_correspondence; [exact (valid_taskset_arrival_curve_correspondence Task tsR tsL _ _ Hts Hma)|].
    apply ar_forall_nat_correspondence. intros DR DL HD.
    apply ar_forall_nat_correspondence. intros CR CL HC.
    apply ar_forall_nat_correspondence. intros PR PL HP.
    exact (osf_monotone_rel _ _ (fifo_blackout_bound_correspondence tsR tsL Hts DR DL CR CL PR PL HD HC HP)).
  Qed.

  Definition src_overheads_sbf_unit : Prop :=
    ltac:(body_of (fun s : S.statement_overheads_sbf_unit => s Task maR)).
  Definition tgt_overheads_sbf_unit : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Overheads_Sbf_Fifo_overheads_sbf_unit Task dT maL)).
  Theorem overheads_sbf_unit_correspondence : PropSPropRel src_overheads_sbf_unit tgt_overheads_sbf_unit.
  Proof.
    unfold src_overheads_sbf_unit, tgt_overheads_sbf_unit.
    apply osf_forall_list. intros tsR tsL Hts.
    apply ar_imp_correspondence; [exact (valid_taskset_arrival_curve_correspondence Task tsR tsL _ _ Hts Hma)|].
    apply ar_forall_nat_correspondence. intros DR DL HD.
    apply ar_forall_nat_correspondence. intros CR CL HC.
    apply ar_forall_nat_correspondence. intros PR PL HP.
    unfold prosa.analysis.definitions.sbf.pred.unit_supply_bound_function.
    cbn [I.Prosa_Analysis_Definitions_Sbf_Pred_unit_supply_bound_function].
    apply ar_forall_nat_correspondence. intros dR dL Hd.
    have Hf := fifo_ovh_sbf_slow_correspondence tsR tsL Hts DR DL CR CL PR PL HD HC HP.
    exact (sub_nat_le_correspondence _ _ _ _ (Hf _ _ (pp_succ_related _ _ Hd)) (pp_succ_related _ _ (Hf _ _ Hd))).
  Qed.
End Defs.

Section Busy.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
  Let PR := prosa.model.processor.overheads.processor_state Job.
  Let PL := I.Prosa_Model_Processor_Overheads_processor_state Job dJ.
  Let X := ovh_psrel Job.
  Variable maR : prosa.model.task.arrival.curves.MaxArrivals Task.
  Variable maL : I.Prosa_Model_Task_Arrival_Curves_MaxArrivals Task dT.
  Hypothesis Hma : CvMaxArrivalsRel Task maR maL.

  Local Ltac imp H := apply ar_imp_correspondence; [exact H|].

  Lemma osf_forall_ja (P : prosa.behavior.job.JobArrival Job -> Prop)
      (Q : I.Prosa_Behavior_Job_JobArrival Job dJ -> SProp) :
    (forall a b, ArJobArrivalRel Job a b -> PropSPropRel (P a) (Q b)) ->
    PropSPropRel (forall a, P a) (forall b, Q b).
  Proof.
    exact (isj_forall_cover_sprop _ _ (ArJobArrivalRel Job) (ar_import_job_arrival Job)
      (svc_export_job_arrival Job) (ar_job_arrival_import_certificate Job) (svc_job_arrival_export Job) P Q).
  Qed.

  Lemma osf_forall_cost (P : prosa.behavior.job.JobCost Job -> Prop)
      (Q : I.Prosa_Behavior_Job_JobCost Job dJ -> SProp) :
    (forall a b, SvcJobCostRel Job a b -> PropSPropRel (P a) (Q b)) ->
    PropSPropRel (forall a, P a) (forall b, Q b).
  Proof.
    exact (isj_forall_cover_sprop _ _ (SvcJobCostRel Job) (svc_import_job_cost Job)
      (svc_export_job_cost Job) (svc_job_cost_import Job) (svc_job_cost_export Job) P Q).
  Qed.

  Definition OsfJobTaskRel (jtR : prosa.model.task.concept.JobTask Job Task)
      (jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT) : SProp :=
    forall j : Job, Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).

  Lemma osf_forall_jt (P : prosa.model.task.concept.JobTask Job Task -> Prop)
      (Q : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT -> SProp) :
    (forall a b, OsfJobTaskRel a b -> PropSPropRel (P a) (Q b)) ->
    PropSPropRel (forall a, P a) (forall b, Q b).
  Proof.
    apply (isj_forall_cover_sprop _ _ OsfJobTaskRel
      (fun jtR => I.Prosa_Model_Task_Concept_JobTask_mk Job dJ Task dT
        (fun j => @prosa.model.task.concept.job_task Job Task jtR j))
      (fun jtL => ((fun j => I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j)
        : prosa.model.task.concept.JobTask Job Task))).
    - intros jtR j. exact (@Lean.eq_refl _ _).
    - intros jtL j. exact (@Lean.eq_refl _ _).
  Qed.

  Lemma osf_ovh_sched sR sL (Hs : IsjPSchedRel Job PR PL X sR sL) : OVC.OvhScheduleRel Job sR sL.
  Proof.
    intros tR tL Ht.
    refine (sub_imported_eq_trans _ _ _ _ (Hs tR tL Ht)). cbn.
    destruct (sR tR) as [| a b | a | j | j]; cbn; try destruct a; try destruct b; exact (@Lean.eq_refl _ _).
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

      Lemma osf_basic_ready_rel :
        FpreJrAt Job jaR jaL costR costL PR PL sR sL
          (@prosa.model.readiness.basic.basic_ready_instance Job PR jaR costR)
          (I.Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job dJ PL jaL costL).
      Proof.
        intros j tR tL Ht.
        exact (fpre_pending_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs j tR tL Ht).
      Qed.

      Lemma osf_preempted_at_related (j : Job) tR tL (Ht : SubNatRel tR tL) :
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

      Lemma osf_no_superfluous_rel pR pL (Hp : FpreJLFPRel Job pR pL) :
        PropSPropRel
          (@PP.no_superfluous_preemptions Job costR (@prosa.model.priority.coercion.JLFP_to_JLDP Job pR) PR sR)
          (I.Prosa_Model_Preemption_Parameter_no_superfluous_preemptions_inst4 Job dJ costL
            (I.Prosa_Model_Priority_Coercion_JLFP_to_JLDP Job dJ pL) PL sL).
      Proof.
        unfold PP.no_superfluous_preemptions.
        cbn [I.Prosa_Model_Preemption_Parameter_no_superfluous_preemptions_inst4].
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_forall_identity_correspondence. intro j.
        apply ar_forall_identity_correspondence. intro jhp.
        apply ar_imp_correspondence;
          [exact (ar_bool_truth_correspondence _ _ (osf_preempted_at_related j tR tL Ht))|].
        apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hsa jhp tR tL Ht))|].
        exact (ar_bool_truth_correspondence _ _ (svc_bool_not_related _ _ (Hp j jhp))).
      Qed.

      Lemma osf_supply_at_related tR tL :
        SubNatRel tR tL ->
        SubNatRel (@prosa.model.processor.supply.supply_at Job PR sR tR)
          (I.Prosa_Validation_SupplyInterface_supplyAtProjection_inst4 Job dJ PL sL tL).
      Proof.
        intro Ht. unfold prosa.model.processor.supply.supply_at.
        cbn [I.Prosa_Validation_SupplyInterface_supplyAtProjection_inst4].
        exact (isj_lean_transport
          (fun s => SubNatRel (@prosa.behavior.schedule.supply_in Job PR (sR tR))
             (I.Prosa_Behavior_Schedule_ProcessorState_supply_in_inst4 Job dJ PL s))
          _ _ (Hs tR tL Ht) (isj_sup_in_rel Job PR PL X (sR tR))).
      Qed.

      Lemma osf_supply_during_related t1R t1L t2R t2L :
        SubNatRel t1R t1L -> SubNatRel t2R t2L ->
        SubNatRel (@prosa.model.processor.supply.supply_during Job PR sR t1R t2R)
          (I.Prosa_Model_Processor_Supply_supply_during_inst4 Job dJ PL sL t1L t2L).
      Proof.
        intros H1 H2. unfold prosa.model.processor.supply.supply_during.
        apply svc_interval_sum_related; [exact H1|exact H2|].
        intros tR tL Ht. exact (osf_supply_at_related tR tL Ht).
      Qed.

      Section BusyPred.
        Variable jtR : prosa.model.task.concept.JobTask Job Task.
        Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
        Hypothesis Hjt : OsfJobTaskRel jtR jtL.
        Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
        Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
        Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.
        Variable pR : prosa.model.priority.definitions.JLFP_policy Job.
        Variable pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
        Hypothesis Hp : FpreJLFPRel Job pR pL.

        Lemma osf_job_of_task_related (tsk : Task) (j : Job) :
          ArBoolRel (@prosa.model.task.concept.job_of_task Job Task jtR tsk j)
            (I.Prosa_Model_Task_Concept_job_of_task Job dJ Task dT jtL tsk j).
        Proof.
          unfold prosa.model.task.concept.job_of_task.
          cbn [I.Prosa_Model_Task_Concept_job_of_task].
          refine (isj_lean_transport
            (fun v => ArBoolRel (@prosa.model.task.concept.job_task Job Task jtR j == tsk)
              (I.Decidable_decide (Lean.eq v tsk) (dT v tsk))) _ _ (Hjt j) _).
          exact (ari_decide_eq_related Task _ tsk).
        Qed.

        Lemma osf_valid_busy_sbf_rel (tsk : Task) fR fL (Hf : SubNatFunRel fR fL) :
          PropSPropRel (@SB.valid_busy_sbf Task Job jaR costR jtR PR arrR sR pR tsk fR)
            (I.Prosa_Analysis_Definitions_Sbf_Busy_valid_busy_sbf_inst8 Task dT Job dJ jaL costL jtL PL arrL sL pL tsk fL).
        Proof.
          unfold SB.valid_busy_sbf, prosa.analysis.definitions.sbf.pred.valid_pred_sbf,
            prosa.analysis.definitions.sbf.pred.pred_sbf_respected.
          cbn [I.Prosa_Analysis_Definitions_Sbf_Busy_valid_busy_sbf_inst8
            I.Prosa_Analysis_Definitions_Sbf_Pred_valid_pred_sbf_inst4
            I.Prosa_Analysis_Definitions_Sbf_Pred_pred_sbf_respected_inst4].
          apply ar_and_correspondence.
          { exact (sub_nat_eq_correspondence _ _ _ _ (Hf _ _ (sub_nat_rel_canonical 0)) (sub_nat_rel_canonical 0)). }
          apply ar_forall_identity_correspondence. intro j.
          apply ar_forall_nat_correspondence. intros t1R t1L H1.
          apply ar_forall_nat_correspondence. intros t2R t2L H2.
          imp (arrives_in_correspondence_certificate Job arrR arrL j Harr).
          apply ar_imp_correspondence.
          { apply ar_and_correspondence.
            - exact (ar_bool_truth_correspondence _ _ (osf_job_of_task_related tsk j)).
            - exact (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr
                pR pL Hp j t1R t1L t2R t2L H1 H2). }
          apply ar_forall_nat_correspondence. intros tR tL Ht.
          apply ar_imp_correspondence;
            [exact (osf_andb_and _ _ _ _ (sub_nat_le_correspondence _ _ _ _ H1 Ht) (sub_nat_le_correspondence _ _ _ _ Ht H2))|].
          exact (sub_nat_le_correspondence _ _ _ _ (Hf _ _ (svc_target_sub_related _ _ _ _ Ht H1))
            (osf_supply_during_related _ _ _ _ H1 Ht)).
        Qed.
      End BusyPred.
    End Pair.

    Lemma osf_all_jobs_from_taskset_related jtR jtL (Hjt : OsfJobTaskRel jtR jtL)
        arrR arrL (Harr : ArArrivalSequenceRel Job arrR arrL) tsR tsL :
      ArListRel tsR tsL ->
      PropSPropRel (@prosa.model.task.concept.all_jobs_from_taskset Task Job jtR arrR tsR)
        (I.Prosa_Model_Task_Concept_all_jobs_from_taskset Task dT Job dJ jtL arrL tsL).
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

  Definition src_overheads_sbf_busy_valid : Prop :=
    ltac:(body_of (fun s : S.statement_overheads_sbf_busy_valid => s Task maR Job)).
  Definition tgt_overheads_sbf_busy_valid : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Overheads_Sbf_Fifo_overheads_sbf_busy_valid Task dT maL Job dJ)).
  Theorem overheads_sbf_busy_valid_correspondence :
    PropSPropRel src_overheads_sbf_busy_valid tgt_overheads_sbf_busy_valid.
  Proof.
    unfold src_overheads_sbf_busy_valid, tgt_overheads_sbf_busy_valid.
    apply osf_forall_jt; intros jtR jtL Hjt.
    apply osf_forall_ja; intros jaR jaL Hja.
    apply osf_forall_cost; intros costR costL Hcost.
    apply (fpre_forall_jp Job); intros jpR jpL Hjp.
    apply (fpre_forall_jlfp Job); intros pR pL Hp.
    apply ar_imp_correspondence.
    { unfold prosa.model.priority.definitions.policy_is_FIFO.
      cbn [I.Prosa_Model_Priority_Definitions_policy_is_FIFO].
      apply ar_forall_identity_correspondence. intro j1.
      apply ar_forall_identity_correspondence. intro j2.
      exact (ar_bool_eq_correspondence _ _ _ _ (Hp j1 j2) (ar_decide_le_related _ _ _ _ (Hja j1) (Hja j2))). }
    apply (fpre_forall_arr Job); intros arrR arrL Harr.
    imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
    apply (fpre_forall_sched Job PR PL X); intros sR sL Hs.
    imp (fpre_valid_schedule_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr _ _
      (osf_basic_ready_rel jaR jaL Hja costR costL Hcost sR sL Hs)).
    imp (ex_work_conserving_related Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr _ _
      (osf_basic_ready_rel jaR jaL Hja costR costL Hcost sR sL Hs)).
    imp (osf_no_superfluous_rel costR costL Hcost sR sL Hs pR pL Hp).
    imp (fpre_respects_jlfp_rel Job jaR jaL costR costL PR PL X sR sL Hs arrR arrL Harr _ _
      (osf_basic_ready_rel jaR jaL Hja costR costL Hcost sR sL Hs) jpR jpL Hjp pR pL Hp).
    imp (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR arrL Harr jpR jpL Hjp).
    apply osf_forall_list. intros tsR tsL Hts.
    imp (osf_all_jobs_from_taskset_related jtR jtL Hjt arrR arrL Harr tsR tsL Hts).
    imp (taskset_respects_max_arrivals_correspondence Task Job jtR jtL Hjt arrR arrL Harr tsR tsL Hts maR maL Hma).
    apply ar_imp_correspondence.
    { apply ar_forall_identity_correspondence. intro j.
      imp (arrives_in_correspondence_certificate Job arrR arrL j Harr).
      exact (ar_bool_truth_correspondence _ _ (ex_job_cost_positive_related Job costR costL Hcost j)). }
    apply ar_forall_nat_correspondence. intros DR DL HD.
    apply ar_forall_nat_correspondence. intros CR CL HC.
    apply ar_forall_nat_correspondence. intros PRb PLb HP.
    imp (ORM.overhead_resource_model_correspondence Job sR sL (osf_ovh_sched sR sL Hs) _ _ _ _ _ _ HD HC HP).
    apply ar_forall_identity_correspondence. intro tsk.
    exact (osf_valid_busy_sbf_rel jaR jaL Hja costR costL Hcost sR sL Hs jtR jtL Hjt arrR arrL Harr pR pL Hp tsk _ _
      (fifo_ovh_sbf_slow_correspondence Task maR maL Hma tsR tsL Hts DR DL CR CL PRb PLb HD HC HP)).
  Qed.
End Busy.
