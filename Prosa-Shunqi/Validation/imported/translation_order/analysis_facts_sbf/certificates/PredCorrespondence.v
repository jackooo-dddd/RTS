(* Re-bound copy of accepted certificates/analysis/PredCorrespondence.v for the analysis/facts/SBF artifact;
   only the imported module name differs. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From prosa Require Import analysis.definitions.sbf.pred.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSbfFacts ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence
  ArrivalSequenceBaseAdapter ArrivalSequenceOperations ArrivalSequenceCorrespondence
  SupplyBaseAdapter SupplyScheduleBaseAdapter SupplyScheduleFiniteOperations
  SupplyScheduleOperations SupplyNatBoolOperations SupplyIntervalOperations
  SupplyCorrespondence.

(** Ordinary related-input relations, not unproved semantic dependencies. *)
Definition PredFunctionRel (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat) :
    SProp :=
  forall nR nL, SubNatRel nR nL -> SubNatRel (fR nR) (fL nL).

Definition PredPredicateRel (Job : eqType)
    (PR : Job -> nat -> nat -> Prop)
    (PL : Job -> Lean.Nat -> Lean.Nat -> SProp) : Prop :=
  forall j t1R t1L t2R t2L,
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    PropSPropRel (PR j t1R t2R) (PL j t1L t2L).

Lemma pred_sbf_is_monotone_correspondence
    (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat) :
  PredFunctionRel fR fL ->
  PropSPropRel
    (prosa.analysis.definitions.sbf.pred.sbf_is_monotone fR)
    (ImportedSbfFacts.Prosa_Analysis_Definitions_Sbf_Pred_sbf_is_monotone fL).
Proof.
  intro Hf.
  unfold prosa.analysis.definitions.sbf.pred.sbf_is_monotone.
  cbn [ImportedSbfFacts.Prosa_Analysis_Definitions_Sbf_Pred_sbf_is_monotone
    ImportedSbfFacts.Prosa_Util_Rel_monotone_inst1].
  apply prop_sprop_rel_intro.
  - intros Hmono xL yL Hxy.
    pose xR := sub_nat_to_rocq xL.
    pose yR := sub_nat_to_rocq yL.
    have Hx : SubNatRel xR xL := sub_nat_rel_surjective xL.
    have Hy : SubNatRel yR yL := sub_nat_rel_surjective yL.
    have Hinput := ar_bool_truth_correspondence _ _
      (ar_decide_le_related _ _ _ _ Hx Hy).
    have Houtput := ar_bool_truth_correspondence _ _
      (ar_decide_le_related _ _ _ _ (Hf _ _ Hx) (Hf _ _ Hy)).
    exact (prop_to_sprop _ _ Houtput
      (Hmono xR yR (sprop_to_prop _ _ Hinput Hxy))).
  - intro Hmono. apply strictly_inhabits.
    intros xR yR Hxy.
    pose xL := sub_nat_to_imported xR.
    pose yL := sub_nat_to_imported yR.
    have Hx : SubNatRel xR xL := sub_nat_rel_canonical xR.
    have Hy : SubNatRel yR yL := sub_nat_rel_canonical yR.
    have Hinput := ar_bool_truth_correspondence _ _
      (ar_decide_le_related _ _ _ _ Hx Hy).
    have Houtput := ar_bool_truth_correspondence _ _
      (ar_decide_le_related _ _ _ _ (Hf _ _ Hx) (Hf _ _ Hy)).
    exact (sprop_to_prop _ _ Houtput
      (Hmono xL yL (prop_to_sprop _ _ Hinput Hxy))).
Qed.

Lemma pred_unit_supply_bound_function_correspondence
    (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat) :
  PredFunctionRel fR fL ->
  PropSPropRel
    (prosa.analysis.definitions.sbf.pred.unit_supply_bound_function fR)
    (ImportedSbfFacts.Prosa_Analysis_Definitions_Sbf_Pred_unit_supply_bound_function fL).
Proof.
  intro Hf.
  unfold prosa.analysis.definitions.sbf.pred.unit_supply_bound_function.
  cbn [ImportedSbfFacts.Prosa_Analysis_Definitions_Sbf_Pred_unit_supply_bound_function].
  apply ar_forall_nat_correspondence. intros dR dL Hd.
  have Hsuccessor := svc_target_add_related dR dL 1 svc_target_one
    Hd (sub_nat_rel_canonical 1).
  have Hleft := Hf _ _ Hsuccessor.
  have Hright := svc_target_add_related (fR dR) (fL dL) 1 svc_target_one
    (Hf _ _ Hd) (sub_nat_rel_canonical 1).
  rewrite !addn1 in Hleft Hright.
  exact (sub_nat_le_correspondence _ _ _ _ Hleft Hright).
Qed.

(** MathComp's chained comparison is a Boolean conjunction.  The target
    elaborates the two Nat comparisons as a proposition-valued conjunction. *)
Lemma pred_andb_truth (a b : bool) :
  is_true (a && b) <-> is_true a /\ is_true b.
Proof. destruct a, b; cbn; firstorder. Qed.

Lemma pred_interval_correspondence
    (t1R tR t2R : nat) (t1L tL t2L : Lean.Nat) :
  SubNatRel t1R t1L -> SubNatRel tR tL -> SubNatRel t2R t2L ->
  PropSPropRel
    (is_true ((leq t1R tR) && (leq tR t2R)))
    (And (ar_target_le t1L tL) (ar_target_le tL t2L)).
Proof.
  intros Ht1 Ht Ht2.
  pose Hfirst := sub_nat_le_correspondence _ _ _ _ Ht1 Ht.
  pose Hsecond := sub_nat_le_correspondence _ _ _ _ Ht Ht2.
  apply prop_sprop_rel_intro.
  - intro H. apply (proj1 (pred_andb_truth _ _)) in H.
    destruct H as [Hleft Hright].
    exact (And_intro _ _
      (prop_to_sprop _ _ Hfirst Hleft)
      (prop_to_sprop _ _ Hsecond Hright)).
  - intro H. apply strictly_inhabits.
    apply (proj2 (pred_andb_truth _ _)). split.
    + exact (sprop_to_prop _ _ Hfirst (ImportedSbfFacts.And_left _ _ H)).
    + exact (sprop_to_prop _ _ Hsecond (ImportedSbfFacts.And_right _ _ H)).
Qed.

Section PredicatedSBF.

  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedSbfFacts.Prosa_Behavior_Schedule_ProcessorState Job
      (sch_decidable_eq Job).
  Variable Rstate : SupplyProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : ImportedSbfFacts.Prosa_Behavior_Schedule_schedule Job
    (sch_decidable_eq Job) PStateL.
  Hypothesis Hsched :
    SupplyScheduleRel Job PStateR PStateL Rstate schedR schedL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : ImportedSbfFacts.Prosa_Behavior_Arrival_sequence_arrival_sequence
    Job (ar_decidable_eq Job).
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.
  Variable PR : Job -> nat -> nat -> Prop.
  Variable PL : Job -> Lean.Nat -> Lean.Nat -> SProp.
  Hypothesis HP : PredPredicateRel Job PR PL.
  Variable fR : nat -> nat.
  Variable fL : Lean.Nat -> Lean.Nat.
  Hypothesis Hf : PredFunctionRel fR fL.

  Lemma pred_sbf_respected_correspondence :
    PropSPropRel
      (@prosa.analysis.definitions.sbf.pred.pred_sbf_respected
        Job PStateR arrR schedR PR fR)
      (ImportedSbfFacts.Prosa_Analysis_Definitions_Sbf_Pred_pred_sbf_respected
        Job (sch_decidable_eq Job) PStateL arrL schedL PL fL).
  Proof.
    unfold prosa.analysis.definitions.sbf.pred.pred_sbf_respected.
    cbn [ImportedSbfFacts.Prosa_Analysis_Definitions_Sbf_Pred_pred_sbf_respected].
    apply ar_forall_identity_correspondence. intro j.
    apply ar_forall_nat_correspondence. intros t1R t1L Ht1.
    apply ar_forall_nat_correspondence. intros t2R t2L Ht2.
    apply ar_imp_correspondence.
    - exact (arrives_in_correspondence_certificate Job arrR arrL j Harr).
    - apply ar_imp_correspondence.
      + exact (HP j t1R t1L t2R t2L Ht1 Ht2).
      + apply ar_forall_nat_correspondence. intros tR tL Ht.
        apply ar_imp_correspondence.
        * exact (pred_interval_correspondence
            t1R tR t2R t1L tL t2L Ht1 Ht Ht2).
        * have Hsub := svc_target_sub_related tR tL t1R t1L Ht Ht1.
          have Hvalue := Hf _ _ Hsub.
          have Hsupply := supply_during_correspondence
            Job PStateR PStateL Rstate schedR schedL Hsched
            t1R tR t1L tL Ht1 Ht.
          exact (sub_nat_le_correspondence _ _ _ _ Hvalue Hsupply).
  Qed.

  Lemma pred_valid_pred_sbf_correspondence :
    PropSPropRel
      (@prosa.analysis.definitions.sbf.pred.valid_pred_sbf
        Job PStateR arrR schedR PR fR)
      (ImportedSbfFacts.Prosa_Analysis_Definitions_Sbf_Pred_valid_pred_sbf
        Job (sch_decidable_eq Job) PStateL arrL schedL PL fL).
  Proof.
    unfold prosa.analysis.definitions.sbf.pred.valid_pred_sbf.
    cbn [ImportedSbfFacts.Prosa_Analysis_Definitions_Sbf_Pred_valid_pred_sbf].
    apply ar_and_correspondence.
    - apply sub_nat_eq_correspondence.
      + exact (Hf O svc_target_zero (sub_nat_rel_canonical O)).
      + exact (sub_nat_rel_canonical O).
    - exact pred_sbf_respected_correspondence.
  Qed.

  Lemma pred_bounded_statement_for_functions :
    PropSPropRel
      ((@prosa.analysis.definitions.sbf.pred.valid_pred_sbf
          Job PStateR arrR schedR PR fR) ->
       prosa.analysis.definitions.sbf.pred.unit_supply_bound_function fR ->
       forall dR : nat, is_true (leq (fR dR) dR))
      ((ImportedSbfFacts.Prosa_Analysis_Definitions_Sbf_Pred_valid_pred_sbf
          Job (sch_decidable_eq Job) PStateL arrL schedL PL fL) ->
       ImportedSbfFacts.Prosa_Analysis_Definitions_Sbf_Pred_unit_supply_bound_function fL ->
       forall dL : Lean.Nat,
         ImportedSbfFacts.LE_le_inst1 Lean.Nat ImportedSbfFacts.instLENat
           (fL dL) dL).
  Proof.
    apply ar_imp_correspondence.
    - exact pred_valid_pred_sbf_correspondence.
    - apply ar_imp_correspondence.
      + exact (pred_unit_supply_bound_function_correspondence fR fL Hf).
      + apply ar_forall_nat_correspondence. intros dR dL Hd.
        exact (sub_nat_le_correspondence _ _ _ _ (Hf _ _ Hd) Hd).
  Qed.

End PredicatedSBF.

(** The accepted SBF class bridge is instantiated on this imported artifact by
    its observable field.  A related class pair is an ordinary input, not a
    whole-theorem semantic assumption. *)
Definition PredSbfClassRel
    (sR : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction)
    (sL : ImportedSbfFacts.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction) :
    SProp :=
  PredFunctionRel sR
    (ImportedSbfFacts.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function sL).

Section PredTheoremStatement.
  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedSbfFacts.Prosa_Behavior_Schedule_ProcessorState Job
      (sch_decidable_eq Job).
  Variable Rstate : SupplyProcessorStateRel Job PStateR PStateL.
  Variable schedR : @prosa.behavior.schedule.schedule Job PStateR.
  Variable schedL : ImportedSbfFacts.Prosa_Behavior_Schedule_schedule Job
    (sch_decidable_eq Job) PStateL.
  Hypothesis Hsched :
    SupplyScheduleRel Job PStateR PStateL Rstate schedR schedL.
  Variable arrR : prosa.behavior.arrival_sequence.arrival_sequence Job.
  Variable arrL : ImportedSbfFacts.Prosa_Behavior_Arrival_sequence_arrival_sequence
    Job (ar_decidable_eq Job).
  Hypothesis Harr : ArArrivalSequenceRel Job arrR arrL.
  Variable PR : Job -> nat -> nat -> Prop.
  Variable PL : Job -> Lean.Nat -> Lean.Nat -> SProp.
  Hypothesis HP : PredPredicateRel Job PR PL.
  Variable sbfR : prosa.analysis.definitions.sbf.sbf.SupplyBoundFunction.
  Variable sbfL : ImportedSbfFacts.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction.
  Hypothesis Hsbf : PredSbfClassRel sbfR sbfL.

  Lemma pred_sbf_bounded_by_duration_statement_correspondence :
    PropSPropRel
      ((@prosa.analysis.definitions.sbf.pred.valid_pred_sbf
          Job PStateR arrR schedR PR sbfR) ->
       prosa.analysis.definitions.sbf.pred.unit_supply_bound_function sbfR ->
       forall dR : nat, is_true (leq (sbfR dR) dR))
      ((ImportedSbfFacts.Prosa_Analysis_Definitions_Sbf_Pred_valid_pred_sbf
          Job (sch_decidable_eq Job) PStateL arrL schedL PL
          (ImportedSbfFacts.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function
            sbfL)) ->
       ImportedSbfFacts.Prosa_Analysis_Definitions_Sbf_Pred_unit_supply_bound_function
         (ImportedSbfFacts.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function
           sbfL) ->
       forall dL : Lean.Nat,
         ImportedSbfFacts.LE_le_inst1 Lean.Nat ImportedSbfFacts.instLENat
           (ImportedSbfFacts.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function
             sbfL dL) dL).
  Proof.
    exact (pred_bounded_statement_for_functions
      Job PStateR PStateL Rstate schedR schedL Hsched
      arrR arrL Harr PR PL HP sbfR
      (ImportedSbfFacts.Prosa_Analysis_Definitions_Sbf_SupplyBoundFunction_supply_bound_function sbfL)
      Hsbf).
  Qed.
End PredTheoremStatement.
