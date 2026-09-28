From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import PiCondSemanticSource.
From prosa Require Import behavior.all model.processor.platform_properties model.schedule.scheduled
  model.priority.classes model.job.properties analysis.definitions.work_bearing_readiness.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedPiCond ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence ArrivalsCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence
  PreemptionTimeCorrespondence PriorityDrivenCorrespondence PStateCoverHelpers FactsPreemptionHelpers
  WorkloadCorrespondence PriorityInversionCorrespondence ExistenceHelpers HepAtPtHelpers
  TaskPreemptionParametersCorrespondence BusyIntervalPiHelpers.

Module I := ImportedPiCond.
Module S := PiCondSemanticSource.PiCondSemanticSource.
Module PIS := PriorityInversionSemanticSource.PriorityInversionSemanticSource.

(** Statement correspondence for [analysis/facts/busy_interval/pi_cond.v].

    Source side: the extracted statement specialised at its leading inputs
    (job type, arrival and cost classes, arrival sequence); target side: the
    imported Lean theorem type.  Inputs: [job_arrival] by [ArJobArrivalRel],
    [job_cost] by the accepted [SvcJobCostRel], arrival sequences by
    [ArArrivalSequenceRel].  Inputs quantified inside the statement are
    covered in both directions: processor models, schedules, JLFP policies,
    [JobPreemptable] and readiness instances by the accepted conversions of
    the busy-interval family, the job predicate [P] pointwise on Booleans
    ([pc_forall_pred]), jobs (identity) and instants.  The conditional
    priority inversion and its cumulative sum are related by replaying the
    accepted priority-inversion definition certificate over the
    processor-model pair (the cumulative sum through its kernel-guarded
    projection); the unconditional ones are the accepted
    busy-interval-existence helpers.  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma pc_forall_pred (Job : eqType) (PRp : pred Job -> Prop) (PLp : (Job -> I.Bool) -> SProp) :
  (forall pR pL, ArPredRel pR pL -> PropSPropRel (PRp pR) (PLp pL)) ->
  PropSPropRel (forall p, PRp p) (forall p, PLp p).
Proof.
  apply (isj_forall_cover_sprop _ _ (fun (pR : pred Job) (pL : Job -> I.Bool) => ArPredRel pR pL)
    (fun pR x => ar_bool_to_imported (pR x)) (fun pL x => ar_bool_to_rocq (pL x))).
  - intros pR x. exact (@Lean.eq_refl _ _).
  - intros pL x. exact (ar_bool_target_roundtrip _).
Qed.

Section PiCond.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.

  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Section Pair.
    Variable PR : prosa.behavior.schedule.ProcessorState Job.
    Variable PL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
    Variable X : IsjPSRel Job PR PL.
    Variable sR : @prosa.behavior.schedule.schedule Job PR.
    Variable sL : I.Prosa_Behavior_Schedule_schedule Job dJ PL.
    Hypothesis Hs : IsjPSchedRel Job PR PL X sR sL.
    Variable pR : prosa.model.priority.definitions.JLFP_policy Job.
    Variable pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
    Hypothesis Hp : FpreJLFPRel Job pR pL.
    Variable j : Job.
    Variable PRp : pred Job.
    Variable PLp : Job -> I.Bool.
    Hypothesis HP : ArPredRel PRp PLp.

    Let SCHEDJOBS := isj_scheduled_jobs_at_related Job PR PL sR sL
      (isj_psr_scheduled_at_related Job PR PL X sR sL Hs) arrR arrL Harr.

    (** Replayed from the accepted priority-inversion definition certificate. *)
    Lemma pc_priority_inversion_cond_related (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      ArBoolRel (@PIS.priority_inversion_cond Job PR arrR sR pR j PRp tR)
        (I.Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_cond
          Job dJ PL arrL sL pL j PLp tL).
    Proof.
      intro Ht. unfold PIS.priority_inversion_cond.
      cbn [I.Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_cond].
      have Hl := SCHEDJOBS tR tL Ht.
      apply ar_bool_and_related.
      - exact (svc_bool_not_related _ _ (ar_decide_mem_related Job j _ _ Hl)).
      - apply pi_has_related; [|exact Hl].
        intro jlp. exact (ar_bool_and_related _ _ _ _ (svc_bool_not_related _ _ (Hp jlp j)) (HP jlp)).
    Qed.

    Lemma pc_cumulative_priority_inversion_cond_related (t1R t2R : nat) (t1L t2L : Lean.Nat) :
      SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      SubNatRel (@PIS.cumulative_priority_inversion_cond Job PR arrR sR pR j PRp t1R t2R)
        (I.Prosa_Analysis_Definitions_PriorityInversion_cumulative_priority_inversion_cond
          Job dJ PL arrL sL pL j PLp t1L t2L).
    Proof.
      intros Ht1 Ht2.
      have Hsum := svc_interval_sum_related t1R t2R t1L t2L
        (fun t => nat_of_bool (@PIS.priority_inversion_cond Job PR arrR sR pR j PRp t))
        (fun t => I.Bool_toNat (I.Prosa_Analysis_Definitions_PriorityInversion_priority_inversion_cond
          Job dJ PL arrL sL pL j PLp t))
        Ht1 Ht2
        (fun a b Hab => pi_bool_to_nat_related _ _ (pc_priority_inversion_cond_related a b Hab)).
      change (SubNatRel
        (@PIS.cumulative_priority_inversion_cond Job PR arrR sR pR j PRp t1R t2R)
        (I.Prosa_Validation_PriorityInversionInterface_cumulPriorityInversionCondProjection
          Job dJ PL arrL sL pL j PLp t1L t2L)) in Hsum.
      exact Hsum.
    Qed.
  End Pair.

  Local Ltac imp H := apply ar_imp_correspondence; [exact H|].
  Local Ltac M_va := imp (valid_arrival_sequence_correspondence_certificate Job jaR jaL arrR arrL Hja Harr).
  Local Ltac M_ps := apply (isj_cover_pstate Job); intros PR PL X.
  Local Ltac M_jlfp := apply fpre_forall_jlfp; intros pR pL Hp.
  Local Ltac M_jp := apply fpre_forall_jp; intros jpR jpL Hjp.
  Definition src_cum_task_pi_eq : Prop :=
    ltac:(body_of (fun s : S.statement_cum_task_pi_eq => s Job jaR costR arrR)).
  Definition tgt_cum_task_pi_eq : SProp :=
    ltac:(type_of_term (@I.Prosa_Analysis_Facts_BusyInterval_PiCond_cum_task_pi_eq Job dJ jaL costL arrL)).

  Theorem cum_task_pi_eq_correspondence : PropSPropRel src_cum_task_pi_eq tgt_cum_task_pi_eq.
  Proof.
    unfold src_cum_task_pi_eq, tgt_cum_task_pi_eq.
    ((M_va; M_ps; imp (isj_psr_uniprocessor_related Job PR PL X); (apply (fpre_forall_sched Job PR PL
      X); intros sR sL Hs); M_jlfp); imp (fpre_reflexive_rel Job pR pL Hp); imp (hap_transitive_rel Job
      pR pL Hp); M_jp; imp (fpre_valid_preemption_model_rel Job costR costL Hcost PR PL X sR sL Hs arrR
      arrL Harr jpR jpL Hjp); (apply (fpre_forall_jr Job jaR jaL Hja costR costL Hcost PR PL X sR sL
      Hs); intros jrR jrL Hjr); (imp (ex_work_bearing_related Job jaR jaL Hja costR costL Hcost PR PL X
      sR sL Hs arrR arrL Harr pR pL Hp jrR jrL Hjr); imp (fpre_valid_schedule_rel Job jaR jaL costR
      costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr); imp (fpre_respects_jlfp_rel Job jaR jaL costR
      costL PR PL X sR sL Hs arrR arrL Harr jrR jrL Hjr jpR jpL Hjp pR pL Hp); apply
      ar_forall_identity_correspondence; intro j; imp (arrives_in_correspondence_certificate Job arrR
      arrL j Harr); imp (ar_bool_truth_correspondence _ _ (ex_job_cost_positive_related Job costR costL
      Hcost j)); (apply ar_forall_nat_correspondence; intros t1R t1L Ht1; apply
      ar_forall_nat_correspondence; intros t2R t2L Ht2; imp (ex_busy_interval_prefix_related Job jaR jaL
      Hja costR costL Hcost PR PL X sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _ Ht1 Ht2)))).
    apply ar_forall_identity_correspondence. intro jlp.
    apply (pc_forall_pred Job). intros PRp PLp HP.
    imp (ar_bool_truth_correspondence _ _ (fpre_scheduled_at_related Job PR PL X sR sL Hs jlp _ _ Ht1)).
    imp (ar_bool_truth_correspondence _ _ (HP jlp)).
    exact (sub_nat_eq_correspondence _ _ _ _
      (ex_cumulative_priority_inversion_related Job PR PL X sR sL Hs arrR arrL Harr pR pL Hp j _ _ _ _
        Ht1 Ht2)
      (pc_cumulative_priority_inversion_cond_related PR PL X sR sL Hs pR pL Hp j PRp PLp HP _ _ _ _ Ht1 Ht2)).
  Qed.
End PiCond.
