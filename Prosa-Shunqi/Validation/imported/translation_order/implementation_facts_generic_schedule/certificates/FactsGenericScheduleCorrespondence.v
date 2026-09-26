From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import FactsGenericScheduleSemanticSource.
From prosa Require Import implementation.definitions.generic_scheduler analysis.definitions.schedule_prefix.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsGenericSchedule ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence
  ArrivalsSeqBaseAdapter ArrivalsSeqOperations ArrivalsSeqCorrespondence
  JitterSvcBaseAdapter JitterSvcNatBoolOperations JitterSvcIntervalOperations
  JitterSvcScheduleOperations JitterSvcJobOperations.

Module I := ImportedFactsGenericSchedule.
Module S := FactsGenericScheduleSemanticSource.FactsGenericScheduleSemanticSource.

(** Statement correspondences for [implementation/facts/generic_schedule.v].

    Source side: the extracted statements [S.statement_X] specialised at
    their leading inputs (job type, processor state, pointwise policy and
    idle state); target side: the imported Lean theorem types at related
    inputs: the accepted two-sided [SvcProcessorStateRel], the idle state
    through its state conversion ([Lean.eq]), the policy related (through
    the state conversion) on schedules related through the state conversion
    and related instants.  Instants quantified inside the statements are
    covered in both directions.  [empty_schedule], [replace_at] and the
    structurally recursive [schedule_up_to] are related by case analysis and
    induction closed by kernel-checked Lean equations exported with the
    artifact; the Lean matchers on instants reduce on the canonical Nat
    constructors.  No source or target theorem is used. *)

Ltac body_of f := let T := type of f in match T with _ -> ?B => exact B end.
Ltac type_of_term t := let T := type of t in exact T.

Lemma fgs_lean_transport {A : Type} (P : A -> SProp) (x y : A) :
  Lean.eq x y -> P x -> P y.
Proof. intros H. destruct H. exact (fun p => p). Qed.

Lemma fgs_src_transport {A : Type} (P : A -> SProp) (x y : A) :
  Logic.eq x y -> P x -> P y.
Proof. intro E. destruct E. exact (fun p => p). Qed.

Lemma fgs_nat_input (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL -> Logic.eq (sub_nat_to_rocq nL) nR.
Proof.
  intro H. have E := f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H).
  rewrite sub_nat_rocq_roundtrip in E. exact (Logic.eq_sym E).
Qed.

Section GenericSchedule.
  Context (Job : eqType).
  Let dJ := ar_decidable_eq Job.
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL : I.Prosa_Behavior_Schedule_ProcessorState Job dJ.
  Variable R : SvcProcessorStateRel Job PStateR PStateL.

  Let StateR := @prosa.behavior.schedule.State Job PStateR.
  Let StateL := I.Prosa_Behavior_Schedule_ProcessorState_State Job dJ PStateL.
  Let SchedR := @prosa.behavior.schedule.schedule Job PStateR.
  Let SchedL := I.Prosa_Behavior_Schedule_schedule Job dJ PStateL.
  Let toL := svc_ps_state_to_target Job PStateR PStateL R.

  Definition FgsScheduleFunRel (schedR : SchedR) (schedL : SchedL) : SProp :=
    forall tR tL, SubNatRel tR tL -> Lean.eq (toL (schedR tR)) (schedL tL).

  Lemma fgs_state_eq_correspondence (sR sR' : StateR) (sL sL' : StateL) :
    Lean.eq (toL sR) sL -> Lean.eq (toL sR') sL' ->
    PropSPropRel (sR = sR') (Lean.eq sL sL').
  Proof.
    intros H H'. apply prop_sprop_rel_intro.
    - intro E.
      exact (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ H)
        (sub_imported_eq_trans _ _ _ (coq_eq_to_imported_eq _ _ (f_equal toL E)) H')).
    - intro EL. apply strictly_inhabits.
      have ET := imported_eq_to_coq_eq _ _
        (sub_imported_eq_trans _ _ _ H
          (sub_imported_eq_trans _ _ _ EL (sub_imported_eq_sym _ _ H'))).
      have ES := f_equal (svc_ps_state_to_source Job PStateR PStateL R) ET.
      rewrite !(svc_ps_state_source_roundtrip Job PStateR PStateL R) in ES.
      exact ES.
  Qed.

  Variable policyR : @prosa.implementation.definitions.generic_scheduler.PointwisePolicy Job PStateR.
  Variable policyL : I.Prosa_Implementation_Definitions_GenericScheduler_PointwisePolicy Job dJ PStateL.
  Hypothesis Hpolicy : forall sR sL, FgsScheduleFunRel sR sL ->
    forall tR tL, SubNatRel tR tL -> Lean.eq (toL (policyR sR tR)) (policyL sL tL).
  Variable idleR : StateR.
  Variable idleL : StateL.
  Hypothesis Hidle : Lean.eq (toL idleR) idleL.

  Let ONE := sub_nat_rel_canonical (S O).
  Let HL1 (n : Lean.Nat) : Lean.Nat :=
    I.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat (I.instHAdd_inst1 Lean.Nat I.instAddNat) n
      (I.OfNat_ofNat_inst1 Lean.Nat 1 (I.instOfNatNat 1)).

  Lemma fgs_succ_related (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL -> SubNatRel tR.+1 (HL1 tL).
  Proof.
    intro Ht.
    exact (fgs_src_transport (fun x => SubNatRel x (HL1 tL)) _ _ (addn1 tR)
      (sub_add_correspondence _ _ _ _ Ht (@Lean.eq_refl _ _))).
  Qed.

  (** *** Schedule operations *)

  Let emptyR := @prosa.implementation.definitions.generic_scheduler.empty_schedule Job PStateR idleR.
  Let emptyL := I.Prosa_Implementation_Definitions_GenericScheduler_empty_schedule Job dJ PStateL idleL.
  Let sutR h := @prosa.implementation.definitions.generic_scheduler.schedule_up_to Job PStateR policyR idleR h.
  Let sutL h := I.Prosa_Implementation_Definitions_GenericScheduler_schedule_up_to Job dJ PStateL policyL idleL h.

  Lemma fgs_empty_related : FgsScheduleFunRel emptyR emptyL.
  Proof.
    intros tR tL Ht.
    exact (sub_imported_eq_trans _ _ _ Hidle (sub_imported_eq_sym _ _
      (I.Prosa_Validation_GenericScheduleInterface_production_empty_schedule Job dJ PStateL idleL tL))).
  Qed.

  Lemma fgs_nat_not_eq (tR t'R : nat) (tL t'L : Lean.Nat) :
    SubNatRel tR tL -> SubNatRel t'R t'L -> t'R <> tR -> I.Not (Lean.eq tL t'L).
  Proof.
    intros Ht Ht' NE. unfold I.Not. intro EL.
    refine (match NE _ return I.False with end).
    rewrite -(fgs_nat_input _ _ Ht) -(fgs_nat_input _ _ Ht').
    exact (Logic.eq_sym (f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ EL))).
  Qed.

  Lemma fgs_replace_at_related (sR : SchedR) (sL : SchedL) (t'R : nat) (t'L : Lean.Nat)
      (nsR : StateR) (nsL : StateL) :
    FgsScheduleFunRel sR sL -> SubNatRel t'R t'L -> Lean.eq (toL nsR) nsL ->
    FgsScheduleFunRel (@prosa.analysis.transform.swap.replace_at Job PStateR sR t'R nsR)
      (I.Prosa_Analysis_Transform_Swap_replace_at Job dJ PStateL sL t'L nsL).
  Proof.
    intros Hs Ht' Hns tR tL Ht.
    destruct (@eqP nat t'R tR) as [E|NE].
    - refine (fgs_src_transport (fun o => Lean.eq (toL o) _) nsR _ _ _).
      + subst tR. rewrite /prosa.analysis.transform.swap.replace_at eqxx; reflexivity.
      + subst tR.
        exact (sub_imported_eq_trans _ _ _ Hns (sub_imported_eq_sym _ _
          (I.Prosa_Validation_ReplaceAtInterface_production_replace_at_same Job dJ PStateL sL t'L nsL tL
            (sub_imported_eq_trans _ _ _ (sub_imported_eq_sym _ _ Ht) Ht')))).
    - refine (fgs_src_transport (fun o => Lean.eq (toL o) _) (sR tR) _ _ _).
      + move/eqP: NE => NE. rewrite /prosa.analysis.transform.swap.replace_at (negbTE NE); reflexivity.
      + exact (sub_imported_eq_trans _ _ _ (Hs tR tL Ht) (sub_imported_eq_sym _ _
          (I.Prosa_Validation_ReplaceAtInterface_production_replace_at_other Job dJ PStateL sL t'L nsL tL
            (fgs_nat_not_eq _ _ _ _ Ht Ht' NE)))).
  Qed.

  Lemma fgs_sut_canonical (hR : nat) : FgsScheduleFunRel (sutR hR) (sutL (sub_nat_to_imported hR)).
  Proof.
    induction hR as [|h IH].
    - have H0 := sub_nat_rel_canonical O.
      exact (fgs_lean_transport (fun y => FgsScheduleFunRel (sutR O) y) _ _
        (sub_imported_eq_sym _ _
          (I.Prosa_Validation_GenericScheduleInterface_production_schedule_up_to_zero Job dJ PStateL policyL idleL))
        (fgs_replace_at_related _ _ _ _ _ _ fgs_empty_related H0 (Hpolicy _ _ fgs_empty_related _ _ H0))).
    - have Hh := sub_nat_rel_canonical h.
      have Hh1 := fgs_succ_related _ _ Hh.
      refine (fgs_lean_transport (fun y => FgsScheduleFunRel (sutR h.+1) (sutL y)) _ _
        (sub_imported_eq_sym _ _ Hh1) _).
      exact (fgs_lean_transport (fun y => FgsScheduleFunRel (sutR h.+1) y) _ _
        (sub_imported_eq_sym _ _
          (I.Prosa_Validation_GenericScheduleInterface_production_schedule_up_to_succ Job dJ PStateL policyL idleL
            (sub_nat_to_imported h)))
        (fgs_replace_at_related _ _ _ _ _ _ IH Hh1 (Hpolicy _ _ IH _ _ Hh1))).
  Qed.

  Lemma fgs_sut_related (hR : nat) (hL : Lean.Nat) :
    SubNatRel hR hL -> FgsScheduleFunRel (sutR hR) (sutL hL).
  Proof.
    intro Hh.
    exact (fgs_lean_transport (fun y => FgsScheduleFunRel (sutR hR) (sutL y)) _ _ Hh (fgs_sut_canonical hR)).
  Qed.

  Let SUT hR hL (Hh : SubNatRel hR hL) tR tL (Ht : SubNatRel tR tL) := fgs_sut_related hR hL Hh tR tL Ht.

  (** The prefix [match t with 0 => empty | t'.+1 => schedule_up_to t'] of the
      two statements, against the Lean matchers of the respective theorems. *)

  Lemma fgs_prefix_def_related (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    FgsScheduleFunRel (match tR with O => emptyR | S t' => sutR t' end)
      (I.Prosa_Implementation_Facts_GenericSchedule_schedule_up_to_def_match_1
        (fun _ : I.Prosa_Behavior_Time_instant => SchedL) tL (fun _ : I.Unit => emptyL) (fun t' => sutL t')).
  Proof.
    intro Ht.
    refine (fgs_lean_transport (fun y => FgsScheduleFunRel (match tR with O => emptyR | S t' => sutR t' end)
      (I.Prosa_Implementation_Facts_GenericSchedule_schedule_up_to_def_match_1
        (fun _ : I.Prosa_Behavior_Time_instant => SchedL) y (fun _ : I.Unit => emptyL) (fun t' => sutL t'))) _ _ Ht _).
    destruct tR as [|t].
    - exact fgs_empty_related.
    - exact (fgs_sut_canonical t).
  Qed.

  (** *** Statements *)

  Definition src_schedule_up_to_def : Prop :=
    ltac:(body_of (fun s : S.statement_schedule_up_to_def => s Job PStateR policyR idleR)).
  Definition tgt_schedule_up_to_def : SProp :=
    ltac:(type_of_term (@I.Prosa_Implementation_Facts_GenericSchedule_schedule_up_to_def
      Job dJ PStateL policyL idleL)).
  Theorem schedule_up_to_def_correspondence : PropSPropRel src_schedule_up_to_def tgt_schedule_up_to_def.
  Proof.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    exact (fgs_state_eq_correspondence _ _ _ _ (SUT _ _ Ht _ _ Ht)
      (Hpolicy _ _ (fgs_prefix_def_related _ _ Ht) _ _ Ht)).
  Qed.

  Definition src_schedule_up_to_unfold : Prop :=
    ltac:(body_of (fun s : S.statement_schedule_up_to_unfold => s Job PStateR policyR idleR)).
  Definition tgt_schedule_up_to_unfold : SProp :=
    ltac:(type_of_term (@I.Prosa_Implementation_Facts_GenericSchedule_schedule_up_to_unfold
      Job dJ PStateL policyL idleL)).
  Theorem schedule_up_to_unfold_correspondence : PropSPropRel src_schedule_up_to_unfold tgt_schedule_up_to_unfold.
  Proof.
    apply ar_forall_nat_correspondence. intros hR hL Hh.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    have HP := fgs_prefix_def_related _ _ Hh.
    exact (fgs_state_eq_correspondence _ _ _ _ (SUT _ _ Hh _ _ Ht)
      (fgs_replace_at_related _ _ _ _ _ _ HP Hh (Hpolicy _ _ HP _ _ Hh) _ _ Ht)).
  Qed.

  Definition src_schedule_up_to_widen : Prop :=
    ltac:(body_of (fun s : S.statement_schedule_up_to_widen => s Job PStateR policyR idleR)).
  Definition tgt_schedule_up_to_widen : SProp :=
    ltac:(type_of_term (@I.Prosa_Implementation_Facts_GenericSchedule_schedule_up_to_widen
      Job dJ PStateL policyL idleL)).
  Theorem schedule_up_to_widen_correspondence : PropSPropRel src_schedule_up_to_widen tgt_schedule_up_to_widen.
  Proof.
    apply ar_forall_nat_correspondence. intros hR hL Hh.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Ht Hh)|].
    exact (fgs_state_eq_correspondence _ _ _ _ (SUT _ _ Hh _ _ Ht)
      (SUT _ _ (fgs_succ_related _ _ Hh) _ _ Ht)).
  Qed.

  Definition src_schedule_up_to_empty : Prop :=
    ltac:(body_of (fun s : S.statement_schedule_up_to_empty => s Job PStateR policyR idleR)).
  Definition tgt_schedule_up_to_empty : SProp :=
    ltac:(type_of_term (@I.Prosa_Implementation_Facts_GenericSchedule_schedule_up_to_empty
      Job dJ PStateL policyL idleL)).
  Theorem schedule_up_to_empty_correspondence : PropSPropRel src_schedule_up_to_empty tgt_schedule_up_to_empty.
  Proof.
    apply ar_forall_nat_correspondence. intros hR hL Hh.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ Hh Ht)|].
    exact (fgs_state_eq_correspondence _ _ _ _ (SUT _ _ Hh _ _ Ht) Hidle).
  Qed.

  Definition src_schedule_up_to_prefix_inclusion : Prop :=
    ltac:(body_of (fun s : S.statement_schedule_up_to_prefix_inclusion => s Job PStateR policyR idleR)).
  Definition tgt_schedule_up_to_prefix_inclusion : SProp :=
    ltac:(type_of_term (@I.Prosa_Implementation_Facts_GenericSchedule_schedule_up_to_prefix_inclusion
      Job dJ PStateL policyL idleL)).
  Theorem schedule_up_to_prefix_inclusion_correspondence :
    PropSPropRel src_schedule_up_to_prefix_inclusion tgt_schedule_up_to_prefix_inclusion.
  Proof.
    apply ar_forall_nat_correspondence. intros h1R h1L H1.
    apply ar_forall_nat_correspondence. intros h2R h2L H2.
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ H1 H2)|].
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence; [exact (sub_nat_le_correspondence _ _ _ _ Ht H1)|].
    exact (fgs_state_eq_correspondence _ _ _ _ (SUT _ _ H1 _ _ Ht) (SUT _ _ H2 _ _ Ht)).
  Qed.

  Definition src_schedule_up_to_identical_prefix : Prop :=
    ltac:(body_of (fun s : S.statement_schedule_up_to_identical_prefix => s Job PStateR policyR idleR)).
  Definition tgt_schedule_up_to_identical_prefix : SProp :=
    ltac:(type_of_term (@I.Prosa_Implementation_Facts_GenericSchedule_schedule_up_to_identical_prefix
      Job dJ PStateL policyL idleL)).
  Theorem schedule_up_to_identical_prefix_correspondence :
    PropSPropRel src_schedule_up_to_identical_prefix tgt_schedule_up_to_identical_prefix.
  Proof.
    apply ar_forall_nat_correspondence. intros hR hL Hh.
    apply ar_forall_nat_correspondence. intros tR tL Ht.
    apply ar_imp_correspondence;
      [exact (sub_nat_le_correspondence _ _ _ _ Ht (fgs_succ_related _ _ Hh))|].
    unfold prosa.analysis.definitions.schedule_prefix.identical_prefix.
    cbn [I.Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix].
    apply ar_forall_nat_correspondence. intros sR sL Hs.
    apply ar_imp_correspondence; [exact (sub_nat_lt_correspondence _ _ _ _ Hs Ht)|].
    exact (fgs_state_eq_correspondence _ _ _ _ (SUT _ _ Hh _ _ Hs) (SUT _ _ Hs _ _ Hs)).
  Qed.
End GenericSchedule.
