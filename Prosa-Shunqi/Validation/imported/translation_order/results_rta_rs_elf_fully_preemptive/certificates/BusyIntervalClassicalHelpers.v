(* Helper-only copy of the accepted certificates/analysis_definitions_busy_interval_classical/BusyIntervalClassicalCorrespondence.v, re-bound to this export: truncated before its
   theorem-statement correspondences (whose target statements are not part of this export). *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import BusyIntervalClassicalSemanticSource.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRtaRsElfFullyPreemptive ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations PreemptionParameterCorrespondence.

Module I := ImportedRtaRsElfFullyPreemptive.
Module S := BusyIntervalClassicalSemanticSource.BusyIntervalClassicalSemanticSource.

(** Certificates for [analysis/definitions/busy_interval/classical.v].

    Source side: the extracted byte-identical definition blocks and the
    extracted [quiet_time_P] statement (a [reflect] view in [Type]),
    specialised at its leading inputs; target side: the compiled Lean
    declarations.  Inputs: [job_arrival] by [ArJobArrivalRel], [job_cost] by
    [SvcJobCostRel], processor states by the accepted two-sided
    [SvcProcessorStateRel], schedules by [SvcScheduleRel] (covered in both
    directions through the state maps), arrival sequences by
    [ArArrivalSequenceRel], the JLFP policy pointwise on Booleans (covered in
    both directions).  Arrival predicates and [arrivals_before] are closed by
    the accepted arrival-sequence certificates, [completed_by] by the
    accepted [pp_completed_by_related], [all] by kernel-checked Lean
    constructor equations.  The [Type]-valued [quiet_time_P] statement is
    related by a pair of constructor-preserving maps between [reflect] and
    the imported [BoolReflect] family; no source or target proof is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma bic_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma bic_nat_input (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
Qed.

Lemma bic_false_correspondence : PropSPropRel Logic.False I.False.
Proof.
  apply prop_sprop_rel_intro.
  - intro H. destruct H.
  - intro H. destruct H.
Qed.

Lemma bic_not_correspondence (P : Prop) (PL : SProp) :
  PropSPropRel P PL -> PropSPropRel (~ P) (I.Not PL).
Proof.
  intro HP. unfold I.Not. apply ar_imp_correspondence; [exact HP|].
  exact bic_false_correspondence.
Qed.

Lemma bic_implb_related aR aL bR bL :
  ArBoolRel aR aL -> ArBoolRel bR bL ->
  ArBoolRel (aR ==> bR) (I.Bool_or (I.Bool_not aL) bL).
Proof.
  intros Ha Hb.
  have H : Logic.eq (aR ==> bR) (~~ aR || bR) by destruct aR, bR.
  rewrite H.
  exact (pp_bool_or_related _ _ _ _ (svc_bool_not_related _ _ Ha) Hb).
Qed.

Section All.
  Context (X : Type).
  Variable PR : X -> bool.
  Variable PL : X -> I.Bool.
  Hypothesis HP : forall x, ArBoolRel (PR x) (PL x).

  Lemma bic_all_canonical (xs : seq X) :
    ArBoolRel (all PR xs) (I.List_all X (ar_list_to_imported xs) PL).
  Proof.
    induction xs as [|x xs IH].
    - exact (sub_imported_eq_sym _ _
        (I.Prosa_Validation_BusyIntervalClassicalInterface_production_all_nil X PL)).
    - cbn [all ar_list_to_imported].
      refine (sub_imported_eq_trans _ _ _ _ (sub_imported_eq_sym _ _
        (I.Prosa_Validation_BusyIntervalClassicalInterface_production_all_cons
          X PL x (ar_list_to_imported xs)))).
      exact (ar_bool_and_related _ _ _ _ (HP x) IH).
  Qed.

  Lemma bic_all_related (xsR : seq X) (xsL : I.List X) :
    ArListRel xsR xsL -> ArBoolRel (all PR xsR) (I.List_all X xsL PL).
  Proof.
    intro Hxs.
    exact (sub_imported_eq_trans _ _ _ (bic_all_canonical xsR)
      (sub_imported_eq_congr (fun l => I.List_all X l PL) _ _ Hxs)).
  Qed.
End All.

Section BusyInterval.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Variable jaR : prosa.behavior.job.JobArrival Job.
  Variable jaL : I.Prosa_Behavior_Job_JobArrival Job dJ.
  Hypothesis Hja : ArJobArrivalRel Job jaR jaL.
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job dJ.
  Hypothesis Hcost : SvcJobCostRel Job costR costL.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job dJ.
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Definition BicJLFPRel (pR : prosa.model.priority.definitions.JLFP_policy Job)
      (pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ) : SProp :=
    forall x y : Job,
      ArBoolRel (@prosa.model.priority.definitions.hep_job Job pR x y)
        (I.Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job dJ pL x y).

  Section Sched.
    Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
    Variable schedL : I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
    Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL R schedR schedL.
    Variable pR : prosa.model.priority.definitions.JLFP_policy Job.
    Variable pL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job dJ.
    Hypothesis Hp : BicJLFPRel pR pL.

    Let COMPLETED := pp_completed_by_related Job costR costL Hcost PStateR PStateL R schedR schedL Hsched.

    Theorem quiet_time_correspondence (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      PropSPropRel (@S.quiet_time Job jaR costR PStateR arrR schedR pR j tR)
        (I.Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time
          Job dJ jaL costL PStateL arrL schedL pL j tL).
    Proof.
      intro Ht. unfold S.quiet_time.
      cbn [I.Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time].
      apply ar_forall_identity_correspondence. intro j_hp.
      apply ar_imp_correspondence; [exact (arrives_in_correspondence_certificate Job arrR arrL j_hp Harr)|].
      apply ar_imp_correspondence; [exact (ar_bool_truth_correspondence _ _ (Hp j_hp j))|].
      apply ar_imp_correspondence;
        [exact (ar_bool_truth_correspondence _ _
          (arrived_before_correspondence_certificate Job jaR jaL j_hp Hja tR tL Ht))|].
      exact (ar_bool_truth_correspondence _ _ (COMPLETED j_hp tR tL Ht)).
    Qed.

    Theorem busy_interval_prefix_correspondence (j : Job) t1R t1L t2R t2L :
      SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      PropSPropRel (@S.busy_interval_prefix Job jaR costR PStateR arrR schedR pR j t1R t2R)
        (I.Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix
          Job dJ jaL costL PStateL arrL schedL pL j t1L t2L).
    Proof.
      intros H1 H2. unfold S.busy_interval_prefix.
      cbn [I.Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix].
      apply ar_and_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ H1 H2)|].
      apply ar_and_correspondence; [exact (quiet_time_correspondence j _ _ H1)|].
      apply ar_and_correspondence.
      - apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_imp_correspondence.
        + exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
            (ar_decide_lt_related _ _ _ _ H1 Ht) (ar_decide_lt_related _ _ _ _ Ht H2))).
        + exact (bic_not_correspondence _ _ (quiet_time_correspondence j _ _ Ht)).
      - exact (ar_bool_truth_correspondence _ _ (ar_bool_and_related _ _ _ _
          (ar_decide_le_related _ _ _ _ H1 (Hja j)) (ar_decide_lt_related _ _ _ _ (Hja j) H2))).
    Qed.

    Theorem busy_interval_correspondence (j : Job) t1R t1L t2R t2L :
      SubNatRel t1R t1L -> SubNatRel t2R t2L ->
      PropSPropRel (@S.busy_interval Job jaR costR PStateR arrR schedR pR j t1R t2R)
        (I.Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval
          Job dJ jaL costL PStateL arrL schedL pL j t1L t2L).
    Proof.
      intros H1 H2. unfold S.busy_interval.
      cbn [I.Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval].
      apply ar_and_correspondence; [exact (busy_interval_prefix_correspondence j _ _ _ _ H1 H2)|].
      exact (quiet_time_correspondence j _ _ H2).
    Qed.

    Theorem quiet_time_dec_correspondence (j : Job) (tR : nat) (tL : Lean.Nat) :
      SubNatRel tR tL ->
      ArBoolRel (@S.quiet_time_dec Job costR PStateR arrR schedR pR j tR)
        (I.Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time_dec
          Job dJ costL PStateL arrL schedL pL j tL).
    Proof.
      intro Ht. unfold S.quiet_time_dec.
      cbn [I.Prosa_Analysis_Definitions_BusyInterval_Classical_quiet_time_dec].
      apply bic_all_related.
      - intro j_hp. exact (bic_implb_related _ _ _ _ (Hp j_hp j) (COMPLETED j_hp tR tL Ht)).
      - exact (arrivals_before_correspondence_certificate Job arrR arrL Harr tR tL Ht).
    Qed.
  End Sched.
End BusyInterval.
