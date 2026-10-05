From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import ExceedanceSbfSemanticSource.
From prosa Require Import behavior.all model.processor.ideal_uni_exceed model.processor.supply
  analysis.facts.model.ideal_uni_exceed.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedExceedanceSbf ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ExcArrivalsSeqBaseAdapter ExcArrivalsSeqOperations ExcArrivalsSeqCorrespondence ExcArrivalsCorrespondence
  ExcJitterSvcBaseAdapter ExcJitterSvcNatBoolOperations ExcJitterSvcIntervalOperations
  ExcJitterSvcScheduleOperations ExcJitterSvcJobOperations ExcPreemptionParameterCorrespondence
  ExcPreemptionTimeCorrespondence ExcPriorityDrivenCorrespondence ExcPStateCoverHelpers ExcFactsPreemptionHelpers
  ExcWorkloadCorrespondence ExcPriorityInversionCorrespondence ExcExistenceHelpers ExcHepAtPtHelpers
  ExcTaskPreemptionParametersCorrespondence ExcBusyIntervalPiHelpers ExcStateRel.

Module I := ImportedExceedanceSbf.
Module S := ExceedanceSbfSemanticSource.ExceedanceSbfSemanticSource.
Module SB := SbfBusySemanticSource.SbfBusySemanticSource.

(** Definition and statement correspondences for [analysis/facts/model/exceedance/SBF.v].

    Source side: the extracted definition, the extracted source-local SBF instance [EPS_SBF_inst] (helper block)
    and the extracted statements specialised at their leading type inputs; target side: the compiled Lean
    definitions and the imported Lean theorem types.  The exceedance processor model is fixed on both sides and
    related by [exc_psrel] (ExcStateRel.v: states constructor-wise, the unit core, [service_in]/[supply_in] through
    the kernel-checked closed forms of the validation interface); the generic chain helpers are replayed at its
    universe instance (Exc*.v, see their headers).  Covered in both directions: job-task, job-cost, job-arrival
    instances and JLFP policies (the accepted relations, two-way totals), arrival sequences and schedules; tasks
    and jobs by identity; the exceedance budget, instants and interval lengths by [SubNatRel].  The classical
    [busy_interval_prefix] is the accepted replayed relation; [is_exceedance_exec] is related constructor-wise
    through the schedule relation; [blackout_during]/[supply_during] unfold into the accepted interval-sum,
    [nat_of_bool] and supply relations; [valid_busy_sbf] and [unit_supply_bound_function] unfold as in the
    accepted overheads SBF certificates, with [EPS_SBF_inst] unfolded on both sides.  No source or target theorem
    is used. *)

Local Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Local Ltac type_of_term t := let T := type of t in exact T.

(** Boolean conjunction in Prop position against a Lean conjunction of propositions. *)
Lemma esbf_andb_and (a b : bool) (PL QL : SProp) :
  PropSPropRel (is_true a) PL -> PropSPropRel (is_true b) QL ->
  PropSPropRel (is_true (a && b)) (And PL QL).
Proof.
  intros Ha Hb. have Hab := ar_and_correspondence _ _ _ _ Ha Hb.
  apply prop_sprop_rel_intro.
  - intro H. exact (prop_to_sprop _ _ Hab (andP H)).
  - intro HL. apply strictly_inhabits. apply/andP. exact (sprop_to_prop _ _ Hab HL).
Qed.

(** ** The definition *)

Theorem eps_sbf_correspondence (eR : nat) (eL : Lean.Nat) (He : SubNatRel eR eL) :
  SubNatFunRel (S.eps_sbf eR) (I.Prosa_Analysis_Facts_Model_Exceedance_SBF_eps_sbf eL).
Proof.
  intros dR dL Hd. unfold S.eps_sbf.
  cbn [I.Prosa_Analysis_Facts_Model_Exceedance_SBF_eps_sbf].
  exact (svc_target_sub_related _ _ _ _ Hd He).
Qed.

Lemma esbf_eps_inst_related (eR : nat) (eL : Lean.Nat) (He : SubNatRel eR eL) :
  SubNatFunRel (S.EPS_SBF_inst eR)
    (I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function
      (I.Prosa_Analysis_Facts_Model_Exceedance_SBF_EPS_SBF_inst eL)).
Proof.
  intros dR dL Hd. unfold S.EPS_SBF_inst.
  cbn [I.Prosa_Analysis_Facts_Model_Exceedance_SBF_EPS_SBF_inst
    I.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function].
  exact (eps_sbf_correspondence eR eL He dR dL Hd).
Qed.

Definition src_eps_sbf_is_unit : Prop :=
  ltac:(body_of (fun s : S.statement_eps_sbf_is_unit => s)).
Definition tgt_eps_sbf_is_unit : SProp :=
  ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Exceedance_SBF_eps_sbf_is_unit)).

Theorem eps_sbf_is_unit_correspondence : PropSPropRel src_eps_sbf_is_unit tgt_eps_sbf_is_unit.
Proof.
  unfold src_eps_sbf_is_unit, tgt_eps_sbf_is_unit.
  apply ar_forall_nat_correspondence. intros eR eL He.
  unfold prosa.analysis.definitions.sbf.pred.unit_supply_bound_function.
  cbn [I.Prosa_Analysis_Definitions_Sbf_Pred_unit_supply_bound_function].
  apply ar_forall_nat_correspondence. intros dR dL Hd.
  have Hsbf := esbf_eps_inst_related eR eL He.
  exact (sub_nat_le_correspondence _ _ _ _ (Hsbf _ _ (pp_succ_related _ _ Hd)) (pp_succ_related _ _ (Hsbf _ _ Hd))).
Qed.

(** ** The statements over the exceedance processor *)

Section Busy.
  Context (Task Job : eqType).
  Let dT := ar_decidable_eq Task.
  Let dJ := ar_decidable_eq Job.
  Let PR := prosa.model.processor.ideal_uni_exceed.exceedance_proc_state Job.
  Let PL := I.Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state Job dJ.
  Let X := exc_psrel Job.

  Local Ltac imp H := apply ar_imp_correspondence; [exact H|].

  Lemma esbf_forall_ja (P : prosa.behavior.job.JobArrival Job -> Prop)
      (Q : I.Prosa_Behavior_Job_JobArrival Job dJ -> SProp) :
    (forall a b, ArJobArrivalRel Job a b -> PropSPropRel (P a) (Q b)) ->
    PropSPropRel (forall a, P a) (forall b, Q b).
  Proof.
    exact (isj_forall_cover_sprop _ _ (ArJobArrivalRel Job) (ar_import_job_arrival Job)
      (svc_export_job_arrival Job) (ar_job_arrival_import_certificate Job) (svc_job_arrival_export Job) P Q).
  Qed.

  Lemma esbf_forall_cost (P : prosa.behavior.job.JobCost Job -> Prop)
      (Q : I.Prosa_Behavior_Job_JobCost Job dJ -> SProp) :
    (forall a b, SvcJobCostRel Job a b -> PropSPropRel (P a) (Q b)) ->
    PropSPropRel (forall a, P a) (forall b, Q b).
  Proof.
    exact (isj_forall_cover_sprop _ _ (SvcJobCostRel Job) (svc_import_job_cost Job)
      (svc_export_job_cost Job) (svc_job_cost_import Job) (svc_job_cost_export Job) P Q).
  Qed.

  Definition EsbfJobTaskRel (jtR : prosa.model.task.concept.JobTask Job Task)
      (jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT) : SProp :=
    forall j : Job, Lean.eq (@prosa.model.task.concept.job_task Job Task jtR j)
      (I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j).

  Lemma esbf_forall_jt (P : prosa.model.task.concept.JobTask Job Task -> Prop)
      (Q : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT -> SProp) :
    (forall a b, EsbfJobTaskRel a b -> PropSPropRel (P a) (Q b)) ->
    PropSPropRel (forall a, P a) (forall b, Q b).
  Proof.
    apply (isj_forall_cover_sprop _ _ EsbfJobTaskRel
      (fun jtR => I.Prosa_Model_Task_Concept_JobTask_mk Job dJ Task dT
        (fun j => @prosa.model.task.concept.job_task Job Task jtR j))
      (fun jtL => ((fun j => I.Prosa_Model_Task_Concept_JobTask_job_task Job dJ Task dT jtL j)
        : prosa.model.task.concept.JobTask Job Task))).
    - intros jtR j. exact (@Lean.eq_refl _ _).
    - intros jtL j. exact (@Lean.eq_refl _ _).
  Qed.

  Section Pair.
    Variable sR : @prosa.behavior.schedule.schedule Job PR.
    Variable sL : I.Prosa_Behavior_Schedule_schedule_inst4 Job dJ PL.
    Hypothesis Hs : IsjPSchedRel Job PR PL X sR sL.

    Lemma esbf_is_exceedance_exec_related tR tL :
      SubNatRel tR tL ->
      SvcBoolRel (@prosa.analysis.facts.model.ideal_uni_exceed.is_exceedance_exec Job (sR tR))
        (I.Prosa_Analysis_Facts_Model_IdealUniExceed_is_exceedance_exec Job dJ (sL tL)).
    Proof.
      intro Ht.
      refine (isj_lean_transport
        (fun s => SvcBoolRel (@prosa.analysis.facts.model.ideal_uni_exceed.is_exceedance_exec Job (sR tR))
           (I.Prosa_Analysis_Facts_Model_IdealUniExceed_is_exceedance_exec Job dJ s))
        _ _ (Hs tR tL Ht) _).
      cbn. destruct (sR tR); exact (@Lean.eq_refl _ _).
    Qed.

    Lemma esbf_supply_at_related tR tL :
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

    Lemma esbf_supply_during_related t1R t1L t2R t2L :
      SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      SubNatRel (@prosa.model.processor.supply.supply_during Job PR sR t1R t2R)
        (I.Prosa_Model_Processor_Supply_supply_during_inst4 Job dJ PL sL t1L t2L).
    Proof.
      intros H1 H2. unfold prosa.model.processor.supply.supply_during.
      apply svc_interval_sum_related; [exact H1|exact H2|].
      intros tR tL Ht. exact (esbf_supply_at_related tR tL Ht).
    Qed.

    Lemma esbf_is_blackout_related tR tL :
      SubNatRel tR tL ->
      SvcBoolRel (@prosa.model.processor.supply.is_blackout Job PR sR tR)
        (I.Prosa_Validation_SupplyInterface_isBlackoutProjection_inst4 Job dJ PL sL tL).
    Proof.
      intro Ht. unfold prosa.model.processor.supply.is_blackout, prosa.model.processor.supply.has_supply.
      cbn [I.Prosa_Validation_SupplyInterface_isBlackoutProjection_inst4
        I.Prosa_Validation_SupplyInterface_hasSupplyProjection_inst4].
      exact (svc_bool_not_related _ _ (svc_decide_lt_related _ _ _ _ (sub_nat_rel_canonical 0)
        (esbf_supply_at_related tR tL Ht))).
    Qed.

    Lemma esbf_blackout_related t1R t1L t2R t2L :
      SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      SubNatRel (@prosa.model.processor.supply.blackout_during Job PR sR t1R t2R)
        (I.Prosa_Model_Processor_Supply_blackout_during_inst4 Job dJ PL sL t1L t2L).
    Proof.
      intros H1 H2. unfold prosa.model.processor.supply.blackout_during.
      apply svc_interval_sum_related; [exact H1|exact H2|].
      intros tR tL Ht. exact (isj_bool_to_nat_related _ _ (esbf_is_blackout_related tR tL Ht)).
    Qed.

    Section Inputs.
      Variable jtR : prosa.model.task.concept.JobTask Job Task.
      Variable jtL : I.Prosa_Model_Task_Concept_JobTask Job dJ Task dT.
      Hypothesis Hjt : EsbfJobTaskRel jtR jtL.
      Variable jaR : prosa.behavior.job.JobArrival Job.
      Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
      Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
      Variable costR : prosa.behavior.job.JobCost Job.
      Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
      Hypothesis Hcost : SvcJobCostRel Job costR costL.
      Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
      Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
      Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.
      Variable pR : prosa.model.priority.definitions.JLFP_policy Job.
      Variable pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
      Hypothesis Hp : FpreJLFPRel Job pR pL.

      Lemma esbf_job_of_task_related (tsk : Task) (j : Job) :
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

      Let BIP j t1R t1L t2R t2L (H1 : SubNatRel t1R t1L) (H2 : SubNatRel t2R t2L) :=
        ex_busy_interval_prefix_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr
          pR pL Hp j t1R t1L t2R t2L H1 H2.

      Lemma esbf_valid_busy_sbf_rel (tsk : Task) fR fL (Hf : SubNatFunRel fR fL) :
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
          - exact (ar_bool_truth_correspondence _ _ (esbf_job_of_task_related tsk j)).
          - exact (BIP j t1R t1L t2R t2L H1 H2). }
        apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_imp_correspondence;
          [exact (esbf_andb_and _ _ _ _ (sub_nat_le_correspondence _ _ _ _ H1 Ht) (sub_nat_le_correspondence _ _ _ _ Ht H2))|].
        exact (sub_nat_le_correspondence _ _ _ _ (Hf _ _ (svc_target_sub_related _ _ _ _ Ht H1))
          (esbf_supply_during_related _ _ _ _ H1 Ht)).
      Qed.
    End Inputs.
  End Pair.

  Definition src_blackout_during_bounded : Prop :=
    ltac:(body_of (fun s : S.statement_blackout_during_bounded => s Task Job)).
  Definition tgt_blackout_during_bounded : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Exceedance_SBF_blackout_during_bounded Task dT Job dJ)).

  Theorem blackout_during_bounded_correspondence :
    PropSPropRel src_blackout_during_bounded tgt_blackout_during_bounded.
  Proof.
    unfold src_blackout_during_bounded, tgt_blackout_during_bounded.
    apply esbf_forall_jt; intros jtR jtL Hjt.
    apply esbf_forall_cost; intros costR costL Hcost.
    apply esbf_forall_ja; intros jaR jaL Hja.
    apply (fpre_forall_jlfp Job); intros pR pL Hp.
    apply (fpre_forall_arr Job); intros arrR arrL Harr.
    apply (fpre_forall_sched Job PR PL X); intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros eR eL He.
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence.
    { apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros t1R t1L H1.
      apply ar_forall_nat_correspondence. intros t2R t2L H2.
      imp (arrives_in_correspondence_certificate Job arrR arrL j Harr).
      imp (ar_bool_truth_correspondence _ _ (esbf_job_of_task_related jtR jtL Hjt tsk j)).
      imp (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr
        pR pL Hp j t1R t1L t2R t2L H1 H2).
      refine (sub_nat_le_correspondence _ _ _ _ _ He).
      apply svc_interval_sum_related; [exact H1|exact H2|].
      intros tR tL Ht. exact (isj_bool_to_nat_related _ _ (esbf_is_exceedance_exec_related sR sL Hs tR tL Ht)). }
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros t1R t1L H1.
    apply ar_forall_nat_correspondence. intros t2R t2L H2.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    imp (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    imp (ar_bool_truth_correspondence _ _ (esbf_job_of_task_related jtR jtL Hjt tsk j)).
    imp (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr
      pR pL Hp j t1R t1L t2R t2L H1 H2).
    imp (ar_bool_truth_correspondence _ _
      (ar_bool_and_related _ _ _ _ (ar_decide_le_related _ _ _ _ H1 Ht) (ar_decide_le_related _ _ _ _ Ht H2))).
    exact (sub_nat_le_correspondence _ _ _ _ (esbf_blackout_related sR sL Hs _ _ _ _ H1 Ht) He).
  Qed.

  Definition src_eps_sbf_is_valid : Prop :=
    ltac:(body_of (fun s : S.statement_eps_sbf_is_valid => s Task Job)).
  Definition tgt_eps_sbf_is_valid : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_Model_Exceedance_SBF_eps_sbf_is_valid Task dT Job dJ)).

  Theorem eps_sbf_is_valid_correspondence : PropSPropRel src_eps_sbf_is_valid tgt_eps_sbf_is_valid.
  Proof.
    unfold src_eps_sbf_is_valid, tgt_eps_sbf_is_valid.
    apply esbf_forall_jt; intros jtR jtL Hjt.
    apply esbf_forall_cost; intros costR costL Hcost.
    apply esbf_forall_ja; intros jaR jaL Hja.
    apply (fpre_forall_jlfp Job); intros pR pL Hp.
    apply (fpre_forall_arr Job); intros arrR arrL Harr.
    apply (fpre_forall_sched Job PR PL X); intros sR sL Hs.
    apply ar_forall_nat_correspondence. intros eR eL He.
    apply ar_forall_identity_correspondence. intro tsk.
    apply ar_imp_correspondence.
    { apply ar_forall_identity_correspondence. intro j.
      apply ar_forall_nat_correspondence. intros t1R t1L H1.
      apply ar_forall_nat_correspondence. intros t2R t2L H2.
      imp (arrives_in_correspondence_certificate Job arrR arrL j Harr).
      imp (ar_bool_truth_correspondence _ _ (esbf_job_of_task_related jtR jtL Hjt tsk j)).
      imp (ex_busy_interval_prefix_related Job jaR jaL Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr
        pR pL Hp j t1R t1L t2R t2L H1 H2).
      refine (sub_nat_le_correspondence _ _ _ _ _ He).
      apply svc_interval_sum_related; [exact H1|exact H2|].
      intros tR tL Ht. exact (isj_bool_to_nat_related _ _ (esbf_is_exceedance_exec_related sR sL Hs tR tL Ht)). }
    exact (esbf_valid_busy_sbf_rel sR sL Hs jtR jtL Hjt jaR jaL Hja costR costL Hcost arrR arrL Harr pR pL Hp tsk
      _ _ (esbf_eps_inst_related eR eL He)).
  Qed.
End Busy.
