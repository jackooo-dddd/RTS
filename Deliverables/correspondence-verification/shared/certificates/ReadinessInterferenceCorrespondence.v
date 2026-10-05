From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From prosa Require Import analysis.definitions.readiness_interference.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedReadinessInterference ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  ServiceBaseAdapter ServiceNatBoolOperations ServiceIntervalOperations ServiceScheduleOperations
  AbstractDefinitionsBaseAdapter AbstractDefinitionsClasses AbstractDefinitionsSums
  AbstractDefinitionsBusyInterval PriorityBaseAdapter.

Module I := ImportedReadinessInterference.

(** Correspondence for [analysis/definitions/readiness_interference.v],
    composed from the accepted ArrivalSequence (arrivals_up_to, filter),
    priority (hep_job), Service interval-sum and abstract busy-interval
    certificates re-bound to this artifact.  New here: the [has]/[List.any]
    bridge.  No source or target theorem is used. *)

Lemma ri_bool_or_related (aR bR : bool) (aL bL : I.Bool) :
  ArBoolRel aR aL -> ArBoolRel bR bL -> ArBoolRel (aR || bR) (I.Bool_or aL bL).
Proof.
  unfold ArBoolRel. intros Ha Hb. destruct Ha. destruct Hb.
  destruct aR, bR; exact (@Lean.eq_refl _ _).
Qed.

Lemma ri_has_canonical (T : Type) (PR : T -> bool) (PL : T -> I.Bool) :
  ArPredRel PR PL ->
  forall xs : seq T, ArBoolRel (has PR xs) (I.List_any T (ar_list_to_imported xs) PL).
Proof.
  intros HP xs. induction xs as [|x xs IH].
  - exact (@Lean.eq_refl _ _).
  - exact (ri_bool_or_related _ _ _ _ (HP x) IH).
Qed.

Lemma ri_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma ri_has_related (T : Type) (PR : T -> bool) (PL : T -> I.Bool)
    (xsR : seq T) (xsL : I.List T) :
  ArPredRel PR PL -> ArListRel xsR xsL -> ArBoolRel (has PR xsR) (I.List_any T xsL PL).
Proof.
  intros HP Hxs.
  exact (ri_lean_transport (fun l => ArBoolRel (has PR xsR) (I.List_any T l PL))
    _ _ Hxs (ri_has_canonical T PR PL HP xsR)).
Qed.

Section ReadinessInterference.
  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    I.Prosa_Behavior_Schedule_ProcessorState Job (ad_decidable_eq Job).
  Variable Rservice : SvcProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : I.Prosa_Behavior_Schedule_schedule Job (ad_decidable_eq Job) PStateL.
  Hypothesis Hsched : SvcScheduleRel Job PStateR PStateL Rservice schedR schedL.

  Variable arrivalR : prosa.behavior.job.JobArrival Job.
  Variable arrivalL : I.Prosa_Behavior_Job_JobArrival Job (ad_decidable_eq Job).
  Hypothesis Harrival : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_arrival Job arrivalR j)
      (I.Prosa_Behavior_Job_JobArrival_job_arrival Job (ad_decidable_eq Job) arrivalL j).
  Variable costR : prosa.behavior.job.JobCost Job.
  Variable costL : I.Prosa_Behavior_Job_JobCost Job (ad_decidable_eq Job).
  Hypothesis Hcost : forall j : Job,
    SubNatRel (@prosa.behavior.job.job_cost Job costR j)
      (I.Prosa_Behavior_Job_JobCost_job_cost Job (ad_decidable_eq Job) costL j).

  (** Input relation for the readiness instance: its [job_ready] field on the
      related schedules. *)
  Variable readyR : @prosa.behavior.ready.JobReady Job PStateR costR arrivalR.
  Variable readyL : I.Prosa_Behavior_Ready_JobReady Job (ad_decidable_eq Job)
    PStateL costL arrivalL.
  Hypothesis Hready : forall j tR tL, SubNatRel tR tL ->
    ArBoolRel (@prosa.behavior.ready.job_ready Job PStateR costR arrivalR readyR schedR j tR)
      (I.Prosa_Behavior_Ready_JobReady_job_ready Job (ad_decidable_eq Job) PStateL
        costL arrivalL readyL schedL j tL).

  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : I.Prosa_Behavior_Arrival_sequence_arrival_sequence Job (ad_decidable_eq Job).
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.

  Variable jlfpR : prosa.model.priority.definitions.JLFP_policy Job.
  Variable jlfpL : I.Prosa_Model_Priority_Definitions_JLFP_policy Job (ad_decidable_eq Job).
  Hypothesis Hjlfp : PdJLFPRel Job jlfpR jlfpL.

  Lemma some_hep_job_ready_correspondence (j : Job) (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    ArBoolRel
      (@some_hep_job_ready Job arrivalR costR PStateR readyR arrR schedR jlfpR j tR)
      (I.Prosa_Analysis_Definitions_ReadinessInterference_some_hep_job_ready
        Job (ad_decidable_eq Job) arrivalL costL PStateL readyL arrL schedL jlfpL j tL).
  Proof.
    intro Ht.
    unfold some_hep_job_ready.
    cbn [I.Prosa_Analysis_Definitions_ReadinessInterference_some_hep_job_ready].
    apply ri_has_related.
    - intro j'. exact (Hready j' tR tL Ht).
    - exact (ar_filter_related Job _ _ _ _ (fun j' => Hjlfp j' j)
        (arrivals_up_to_correspondence_certificate Job arrR arrL Harr tR tL Ht)).
  Qed.

  Lemma cumulative_readiness_interference_correspondence (j : Job)
      (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SubNatRel
      (@cumulative_readiness_interference Job arrivalR costR PStateR readyR arrR schedR
        jlfpR j t1R t2R)
      (I.Prosa_Analysis_Definitions_ReadinessInterference_cumulative_readiness_interference
        Job (ad_decidable_eq Job) arrivalL costL PStateL readyL arrL schedL jlfpL j t1L t2L).
  Proof.
    intros Ht1 Ht2.
    have Hsum := svc_interval_sum_related t1R t2R t1L t2L
      (fun t => nat_of_bool (~~ @some_hep_job_ready Job arrivalR costR PStateR readyR
        arrR schedR jlfpR j t))
      (fun t => I.Bool_toNat (I.Bool_not
        (I.Prosa_Analysis_Definitions_ReadinessInterference_some_hep_job_ready
          Job (ad_decidable_eq Job) arrivalL costL PStateL readyL arrL schedL jlfpL j t)))
      Ht1 Ht2
      (fun a b Hab => ad_bool_to_nat_related _ _
        (svc_bool_not_related _ _ (some_hep_job_ready_correspondence j a b Hab))).
    change (SubNatRel
      (@cumulative_readiness_interference Job arrivalR costR PStateR readyR arrR schedR
        jlfpR j t1R t2R)
      (I.Prosa_Validation_ReadinessInterferenceInterface_cumulReadinessInterferenceProjection
        Job (ad_decidable_eq Job) arrivalL costL PStateL readyL arrL schedL jlfpL j t1L t2L))
      in Hsum.
    exact Hsum.
  Qed.

  Variable interR : prosa.analysis.abstract.definitions.Interference Job.
  Variable interL : I.Prosa_Analysis_Abstract_Definitions_Interference Job (ad_decidable_eq Job).
  Hypothesis Hinter : AdInterferenceRel Job interR interL.
  Variable workloadR : prosa.analysis.abstract.definitions.InterferingWorkload Job.
  Variable workloadL :
    I.Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job (ad_decidable_eq Job).
  Hypothesis Hworkload : AdInterferingWorkloadRel Job workloadR workloadL.

  Variable BR : nat -> nat -> nat.
  Variable BL : Lean.Nat -> Lean.Nat -> Lean.Nat.
  Hypothesis HB : forall aR aL bR bL, SubNatRel aR aL -> SubNatRel bR bL ->
    SubNatRel (BR aR bR) (BL aL bL).

  Theorem readiness_interference_is_bounded_correspondence :
    PropSPropRel
      (@readiness_interference_is_bounded Job arrivalR costR PStateR readyR arrR schedR
        jlfpR interR workloadR BR)
      (I.Prosa_Analysis_Definitions_ReadinessInterference_readiness_interference_is_bounded
        Job (ad_decidable_eq Job) arrivalL costL PStateL readyL arrL schedL jlfpL
        interL workloadL BL).
  Proof.
    unfold readiness_interference_is_bounded.
    cbn [I.Prosa_Analysis_Definitions_ReadinessInterference_readiness_interference_is_bounded].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
    apply ar_forall_nat_correspondence. intros dR dL Hd.
    have Hsum := sub_add_correspondence _ _ _ _ Ht1 Hd.
    apply ar_imp_correspondence.
    - exact (sub_nat_le_correspondence _ _ _ _ Hsum Ht2).
    - apply ar_imp_correspondence.
      + exact (ad_busy_interval_prefix_correspondence Job PStateR PStateL Rservice
          schedR schedL Hsched arrivalR arrivalL Harrival costR costL Hcost
          interR interL Hinter workloadR workloadL Hworkload j t1R t2R t1L t2L Ht1 Ht2).
      + exact (sub_nat_le_correspondence _ _ _ _
          (cumulative_readiness_interference_correspondence j _ _ _ _ Ht1 Hsum)
          (HB _ _ _ _ (svc_target_sub_related _ _ _ _ (Harrival j) Ht1) Hd)).
  Qed.
End ReadinessInterference.

Print Assumptions readiness_interference_is_bounded_correspondence.
