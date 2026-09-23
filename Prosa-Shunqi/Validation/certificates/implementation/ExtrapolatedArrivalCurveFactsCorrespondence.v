From mathcomp Require Import ssreflect ssrbool ssrnat seq div.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedExtrapolatedArrivalCurveFactsCombined.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence.
From FactsAdapter Require Import ExtrapolatedArrivalCurveFactsOperationAdapter.
Require Import OfficialExtrapolatedArrivalCurveFacts.
Require Import OfficialExtrapolatedArrivalCurve.
Require Import OfficialRel.

(** These source declarations are signatures extracted from the pinned
    post-Section Rocq types.  No source theorem proof term is imported. *)
Module OF := OfficialExtrapolatedArrivalCurveFacts.OfficialExtrapolatedArrivalCurveFacts.
Module IF := ImportedExtrapolatedArrivalCurveFactsCombined.

Definition FactsStepR := Datatypes.prod nat nat.
Definition FactsStepL := IF.Prod_inst3 Lean.Nat Lean.Nat.

Definition FactsOperationRel
    (rR : FactsStepR -> FactsStepR -> bool)
    (rL : FactsStepL -> FactsStepL -> IF.Bool) : SProp :=
  forall aR bR aL bL,
    Lean.eq (eac_imported_step aR) aL ->
    Lean.eq (eac_imported_step bR) bL ->
    EacBoolRel (rR aR bR) (rL aL bL).

Definition facts_step_truth_correspondence
    (rR : FactsStepR -> FactsStepR -> bool)
    (rL : FactsStepL -> FactsStepL -> IF.Bool)
    (Hop : FactsOperationRel rR rL)
    (aR bR : FactsStepR) (aL bL : FactsStepL)
    (Ha : Lean.eq (eac_imported_step aR) aL)
    (Hb : Lean.eq (eac_imported_step bR) bL) :
    PropSPropRel (is_true (rR aR bR))
      (Lean.eq (rL aL bL) IF.Bool_true) :=
  eac_bool_truth_correspondence _ _ (Hop aR bR aL bL Ha Hb).

Definition facts_transitive_statement_correspondence
    (rR : FactsStepR -> FactsStepR -> bool)
    (rL : FactsStepL -> FactsStepL -> IF.Bool)
    (Hop : FactsOperationRel rR rL) :
    PropSPropRel (transitive rR)
      (forall aL bL cL,
        Lean.eq (rL aL bL) IF.Bool_true ->
        Lean.eq (rL bL cL) IF.Bool_true ->
        Lean.eq (rL aL cL) IF.Bool_true).
Proof.
  apply prop_sprop_rel_intro.
  - intros HR aL bL cL HabL HbcL.
    set (aR := eac_rocq_step aL).
    set (bR := eac_rocq_step bL).
    set (cR := eac_rocq_step cL).
    have Ha := eac_step_imported_roundtrip aL.
    have Hb := eac_step_imported_roundtrip bL.
    have Hc := eac_step_imported_roundtrip cL.
    have Hab := facts_step_truth_correspondence rR rL Hop aR bR aL bL Ha Hb.
    have Hbc := facts_step_truth_correspondence rR rL Hop bR cR bL cL Hb Hc.
    have Hac := facts_step_truth_correspondence rR rL Hop aR cR aL cL Ha Hc.
    exact (prop_to_sprop _ _ Hac
      (HR bR aR cR
        (sprop_to_prop _ _ Hab HabL)
        (sprop_to_prop _ _ Hbc HbcL))).
  - intro HL. apply strictly_inhabits.
    intros bR aR cR HabR HbcR.
    set (aL := eac_imported_step aR).
    set (bL := eac_imported_step bR).
    set (cL := eac_imported_step cR).
    have Ha : Lean.eq (eac_imported_step aR) aL := @Lean.eq_refl _ _.
    have Hb : Lean.eq (eac_imported_step bR) bL := @Lean.eq_refl _ _.
    have Hc : Lean.eq (eac_imported_step cR) cL := @Lean.eq_refl _ _.
    have Hab := facts_step_truth_correspondence rR rL Hop aR bR aL bL Ha Hb.
    have Hbc := facts_step_truth_correspondence rR rL Hop bR cR bL cL Hb Hc.
    have Hac := facts_step_truth_correspondence rR rL Hop aR cR aL cL Ha Hc.
    exact (sprop_to_prop _ _ Hac
      (HL aL bL cL
        (prop_to_sprop _ _ Hab HabR)
        (prop_to_sprop _ _ Hbc HbcR))).
Defined.

Definition facts_reflexive_statement_correspondence
    (rR : FactsStepR -> FactsStepR -> bool)
    (rL : FactsStepL -> FactsStepL -> IF.Bool)
    (Hop : FactsOperationRel rR rL) :
    PropSPropRel (reflexive rR)
      (forall aL, Lean.eq (rL aL aL) IF.Bool_true).
Proof.
  apply prop_sprop_rel_intro.
  - intros HR aL.
    set (aR := eac_rocq_step aL).
    have Ha := eac_step_imported_roundtrip aL.
    have Hrel := facts_step_truth_correspondence rR rL Hop aR aR aL aL Ha Ha.
    exact (prop_to_sprop _ _ Hrel (HR aR)).
  - intro HL. apply strictly_inhabits. intro aR.
    set (aL := eac_imported_step aR).
    have Ha : Lean.eq (eac_imported_step aR) aL := @Lean.eq_refl _ _.
    have Hrel := facts_step_truth_correspondence rR rL Hop aR aR aL aL Ha Ha.
    exact (sprop_to_prop _ _ Hrel (HL aL)).
Defined.

Definition facts_ltn_steps_is_transitive_certificate :
  PropSPropRel OF.statement_ltn_steps_is_transitive
    (forall a b c : FactsStepL,
      Lean.eq (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ltn_steps a b) IF.Bool_true ->
      Lean.eq (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ltn_steps b c) IF.Bool_true ->
      Lean.eq (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ltn_steps a c) IF.Bool_true) :=
  facts_transitive_statement_correspondence _ _ eac_ltn_steps_correspondence.

Definition facts_leq_steps_is_reflexive_certificate :
  PropSPropRel OF.statement_leq_steps_is_reflexive
    (forall a : FactsStepL,
      Lean.eq (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_leq_steps a a) IF.Bool_true) :=
  facts_reflexive_statement_correspondence _ _ eac_leq_steps_correspondence.

Definition facts_leq_steps_is_transitive_certificate :
  PropSPropRel OF.statement_leq_steps_is_transitive
    (forall a b c : FactsStepL,
      Lean.eq (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_leq_steps a b) IF.Bool_true ->
      Lean.eq (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_leq_steps b c) IF.Bool_true ->
      Lean.eq (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_leq_steps a c) IF.Bool_true) :=
  facts_transitive_statement_correspondence _ _ eac_leq_steps_correspondence.

(** A reusable statement shell for two Boolean premises and a Boolean
    conclusion over the already certified prefix representation. *)
Definition FactsPrefixR := OfficialExtrapolatedArrivalCurve.ArrivalCurvePrefix.
Definition FactsPrefixL :=
  IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix.

Definition FactsPrefixBoolRel (rR : FactsPrefixR -> bool)
    (rL : FactsPrefixL -> IF.Bool) : SProp :=
  forall pR pL, EacPrefixRel pR pL -> EacBoolRel (rR pR) (rL pL).

Definition facts_prefix_truth_correspondence
    (rR : FactsPrefixR -> bool) (rL : FactsPrefixL -> IF.Bool)
    (Hr : FactsPrefixBoolRel rR rL) pR pL (Hp : EacPrefixRel pR pL) :
    PropSPropRel (is_true (rR pR)) (Lean.eq (rL pL) IF.Bool_true) :=
  eac_bool_truth_correspondence _ _ (Hr pR pL Hp).

Definition facts_two_premise_bool_statement_correspondence
    (rR sR tR : FactsPrefixR -> bool)
    (rL sL tL : FactsPrefixL -> IF.Bool)
    (Hr : FactsPrefixBoolRel rR rL)
    (Hs : FactsPrefixBoolRel sR sL)
    (Ht : FactsPrefixBoolRel tR tL) :
    PropSPropRel
      (forall pR, rR pR -> sR pR -> tR pR)
      (forall pL, Lean.eq (rL pL) IF.Bool_true ->
        Lean.eq (sL pL) IF.Bool_true ->
        Lean.eq (tL pL) IF.Bool_true).
Proof.
  apply prop_sprop_rel_intro.
  - intros HR pL HrL HsL.
    set (pR := eac_rocq_prefix pL).
    have Hp := eac_prefix_imported_roundtrip pL.
    have Hr' := facts_prefix_truth_correspondence rR rL Hr pR pL Hp.
    have Hs' := facts_prefix_truth_correspondence sR sL Hs pR pL Hp.
    have Ht' := facts_prefix_truth_correspondence tR tL Ht pR pL Hp.
    exact (prop_to_sprop _ _ Ht'
      (HR pR (sprop_to_prop _ _ Hr' HrL)
        (sprop_to_prop _ _ Hs' HsL))).
  - intro HL. apply strictly_inhabits. intros pR HrR HsR.
    set (pL := eac_imported_prefix pR).
    have Hp : EacPrefixRel pR pL := @Lean.eq_refl _ _.
    have Hr' := facts_prefix_truth_correspondence rR rL Hr pR pL Hp.
    have Hs' := facts_prefix_truth_correspondence sR sL Hs pR pL Hp.
    have Ht' := facts_prefix_truth_correspondence tR tL Ht pR pL Hp.
    exact (sprop_to_prop _ _ Ht'
      (HL pL (prop_to_sprop _ _ Hr' HrR)
        (prop_to_sprop _ _ Hs' HsR))).
Defined.

Definition facts_sorted_ltn_implies_sorted_leq_certificate :
  PropSPropRel
    OF.statement_sorted_ltn_steps_imply_sorted_leq_steps_steps
    (forall pL : FactsPrefixL,
      Lean.eq (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sorted_ltn_steps pL) IF.Bool_true ->
      Lean.eq (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_no_inf_arrivals pL) IF.Bool_true ->
      Lean.eq (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sorted_leq_steps pL) IF.Bool_true) :=
  facts_two_premise_bool_statement_correspondence _ _ _ _ _ _
    eac_sorted_ltn_steps_correspondence
    eac_no_inf_arrivals_correspondence
    eac_sorted_leq_steps_correspondence.

Definition FactsPrefixNatFunRel (fR : FactsPrefixR -> nat -> nat)
    (fL : FactsPrefixL -> Lean.Nat -> Lean.Nat) : SProp :=
  forall pR pL, EacPrefixRel pR pL ->
    forall tR tL, SubNatRel tR tL -> SubNatRel (fR pR tR) (fL pL tL).

Definition facts_nat_le_correspondence aR aL bR bL
    (Ha : SubNatRel aR aL) (Hb : SubNatRel bR bL) :
    PropSPropRel (is_true (leq aR bR))
      (IF.LE_le_inst1 Lean.Nat IF.instLENat aL bL) :=
  sub_nat_le_correspondence aR aL bR bL Ha Hb.

Definition facts_monotone_core_correspondence
    (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat)
    (Hf : forall tR tL, SubNatRel tR tL -> SubNatRel (fR tR) (fL tL)) :
    PropSPropRel
      (OfficialRel.OfficialRel.monotone leq fR)
      (forall t1 t2 : Lean.Nat,
        IF.LE_le_inst1 Lean.Nat IF.instLENat t1 t2 ->
        IF.LE_le_inst1 Lean.Nat IF.instLENat (fL t1) (fL t2)).
Proof.
  apply prop_sprop_rel_intro.
  - intros HR t1L t2L HleL.
    set (t1R := sub_nat_to_rocq t1L).
    set (t2R := sub_nat_to_rocq t2L).
    have H1 := sub_nat_imported_roundtrip t1L.
    have H2 := sub_nat_imported_roundtrip t2L.
    have Hle := facts_nat_le_correspondence t1R t1L t2R t2L H1 H2.
    have Hf1 := Hf t1R t1L H1.
    have Hf2 := Hf t2R t2L H2.
    have Hout := facts_nat_le_correspondence _ _ _ _ Hf1 Hf2.
    exact (prop_to_sprop _ _ Hout
      (HR t1R t2R (sprop_to_prop _ _ Hle HleL))).
  - intro HL. apply strictly_inhabits. intros t1R t2R HleR.
    set (t1L := sub_nat_to_imported t1R).
    set (t2L := sub_nat_to_imported t2R).
    have H1 : SubNatRel t1R t1L := @Lean.eq_refl _ _.
    have H2 : SubNatRel t2R t2L := @Lean.eq_refl _ _.
    have Hle := facts_nat_le_correspondence t1R t1L t2R t2L H1 H2.
    have Hf1 := Hf t1R t1L H1.
    have Hf2 := Hf t2R t2L H2.
    have Hout := facts_nat_le_correspondence _ _ _ _ Hf1 Hf2.
    exact (sprop_to_prop _ _ Hout
      (HL t1L t2L (prop_to_sprop _ _ Hle HleR))).
Defined.

Definition facts_one_premise_monotone_correspondence
    (rR : FactsPrefixR -> bool) (rL : FactsPrefixL -> IF.Bool)
    (fR : FactsPrefixR -> nat -> nat)
    (fL : FactsPrefixL -> Lean.Nat -> Lean.Nat)
    (Hr : FactsPrefixBoolRel rR rL)
    (Hf : FactsPrefixNatFunRel fR fL) :
    PropSPropRel
      (forall pR, rR pR -> OfficialRel.OfficialRel.monotone leq (fR pR))
      (forall pL, Lean.eq (rL pL) IF.Bool_true ->
        forall t1 t2 : Lean.Nat,
          IF.LE_le_inst1 Lean.Nat IF.instLENat t1 t2 ->
          IF.LE_le_inst1 Lean.Nat IF.instLENat
            (fL pL t1) (fL pL t2)).
Proof.
  apply prop_sprop_rel_intro.
  - intros HR pL HrL.
    set (pR := eac_rocq_prefix pL).
    have Hp := eac_prefix_imported_roundtrip pL.
    have Hpr := facts_prefix_truth_correspondence rR rL Hr pR pL Hp.
    have Hm := facts_monotone_core_correspondence (fR pR) (fL pL)
      (Hf pR pL Hp).
    exact (prop_to_sprop _ _ Hm (HR pR (sprop_to_prop _ _ Hpr HrL))).
  - intro HL. apply strictly_inhabits. intros pR HrR.
    set (pL := eac_imported_prefix pR).
    have Hp : EacPrefixRel pR pL := @Lean.eq_refl _ _.
    have Hpr := facts_prefix_truth_correspondence rR rL Hr pR pL Hp.
    have Hm := facts_monotone_core_correspondence (fR pR) (fL pL)
      (Hf pR pL Hp).
    exact (sprop_to_prop _ _ Hm
      (HL pL (prop_to_sprop _ _ Hpr HrR))).
Defined.

Definition facts_value_at_monotone_certificate :
  PropSPropRel OF.statement_value_at_monotone
    (forall pL : FactsPrefixL,
      Lean.eq (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sorted_leq_steps pL) IF.Bool_true ->
      forall t1 t2 : Lean.Nat,
        IF.LE_le_inst1 Lean.Nat IF.instLENat t1 t2 ->
        IF.LE_le_inst1 Lean.Nat IF.instLENat
          (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_value_at pL t1)
          (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_value_at pL t2)) :=
  facts_one_premise_monotone_correspondence _ _ _ _
    eac_sorted_leq_steps_correspondence
    (fun pR pL Hp tR tL Ht =>
      eac_value_at_correspondence pR pL tR tL Hp Ht).

Definition facts_two_premise_monotone_correspondence
    (rR sR : FactsPrefixR -> bool)
    (rL sL : FactsPrefixL -> IF.Bool)
    (fR : FactsPrefixR -> nat -> nat)
    (fL : FactsPrefixL -> Lean.Nat -> Lean.Nat)
    (Hr : FactsPrefixBoolRel rR rL)
    (Hs : FactsPrefixBoolRel sR sL)
    (Hf : FactsPrefixNatFunRel fR fL) :
    PropSPropRel
      (forall pR, rR pR -> sR pR ->
        OfficialRel.OfficialRel.monotone leq (fR pR))
      (forall pL,
        Lean.eq (rL pL) IF.Bool_true ->
        Lean.eq (sL pL) IF.Bool_true ->
        forall t1 t2 : Lean.Nat,
          IF.LE_le_inst1 Lean.Nat IF.instLENat t1 t2 ->
          IF.LE_le_inst1 Lean.Nat IF.instLENat
            (fL pL t1) (fL pL t2)).
Proof.
  apply prop_sprop_rel_intro.
  - intros HR pL HrL HsL.
    set (pR := eac_rocq_prefix pL).
    have Hp := eac_prefix_imported_roundtrip pL.
    have Hr' := facts_prefix_truth_correspondence rR rL Hr pR pL Hp.
    have Hs' := facts_prefix_truth_correspondence sR sL Hs pR pL Hp.
    have Hm := facts_monotone_core_correspondence (fR pR) (fL pL)
      (Hf pR pL Hp).
    exact (prop_to_sprop _ _ Hm
      (HR pR (sprop_to_prop _ _ Hr' HrL)
        (sprop_to_prop _ _ Hs' HsL))).
  - intro HL. apply strictly_inhabits. intros pR HrR HsR.
    set (pL := eac_imported_prefix pR).
    have Hp : EacPrefixRel pR pL := @Lean.eq_refl _ _.
    have Hr' := facts_prefix_truth_correspondence rR rL Hr pR pL Hp.
    have Hs' := facts_prefix_truth_correspondence sR sL Hs pR pL Hp.
    have Hm := facts_monotone_core_correspondence (fR pR) (fL pL)
      (Hf pR pL Hp).
    exact (sprop_to_prop _ _ Hm
      (HL pL (prop_to_sprop _ _ Hr' HrR)
        (prop_to_sprop _ _ Hs' HsR))).
Defined.

Definition facts_extrapolated_arrival_curve_is_monotone_certificate :
  PropSPropRel OF.statement_extrapolated_arrival_curve_is_monotone
    (forall pL : FactsPrefixL,
      Lean.eq (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_positive_horizon pL) IF.Bool_true ->
      Lean.eq (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sorted_leq_steps pL) IF.Bool_true ->
      forall t1 t2 : Lean.Nat,
        IF.LE_le_inst1 Lean.Nat IF.instLENat t1 t2 ->
        IF.LE_le_inst1 Lean.Nat IF.instLENat
          (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_extrapolated_arrival_curve pL t1)
          (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_extrapolated_arrival_curve pL t2)) :=
  facts_two_premise_monotone_correspondence _ _ _ _ _ _
    eac_positive_horizon_correspondence
    eac_sorted_leq_steps_correspondence
    (fun pR pL Hp tR tL Ht =>
      eac_extrapolated_arrival_curve_correspondence pR pL tR tL Hp Ht).

(** Pair equality is shared by both step-at theorems.  The backward
    interpretation uses the one explicit Prop/SProp foundation, never a
    theorem-specific semantic axiom. *)
Definition facts_imported_eq_to_prop {A : Type} (x y : A)
    (H : Lean.eq x y) : Logic.eq x y :=
  interpret_strict _ (imported_eq_to_strict_eq x y H).

Definition facts_step_eq_correspondence
    (aR bR : FactsStepR) (aL bL : FactsStepL)
    (Ha : Lean.eq (eac_imported_step aR) aL)
    (Hb : Lean.eq (eac_imported_step bR) bL) :
    PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof.
  apply prop_sprop_rel_intro.
  - intro Heq. subst bR.
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _ Ha) Hb).
  - intro Heq. apply strictly_inhabits.
    have Ha' : Logic.eq (eac_rocq_step aL) aR.
    { have H := facts_imported_eq_to_prop _ _ Ha.
      rewrite <- H. exact (eac_step_rocq_roundtrip aR). }
    have Hb' : Logic.eq (eac_rocq_step bL) bR.
    { have H := facts_imported_eq_to_prop _ _ Hb.
      rewrite <- H. exact (eac_step_rocq_roundtrip bR). }
    rewrite <- Ha', <- Hb'.
    exact (f_equal eac_rocq_step (facts_imported_eq_to_prop _ _ Heq)).
Defined.

Definition facts_step_at_zero_certificate :
  PropSPropRel OF.statement_step_at_0_is_00
    (forall pL : FactsPrefixL,
      Lean.eq (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sorted_ltn_steps pL) IF.Bool_true ->
      Lean.eq (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_no_inf_arrivals pL) IF.Bool_true ->
      Lean.eq
        (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_step_at pL Lean.Nat_zero)
        (IF.Prod_mk_inst3 Lean.Nat Lean.Nat Lean.Nat_zero Lean.Nat_zero)).
Proof.
  apply prop_sprop_rel_intro.
  - intros HR pL HsortedL HnoinfL.
    set (pR := eac_rocq_prefix pL).
    have Hp := eac_prefix_imported_roundtrip pL.
    have Hsorted := facts_prefix_truth_correspondence _ _
      eac_sorted_ltn_steps_correspondence pR pL Hp.
    have Hnoinf := facts_prefix_truth_correspondence _ _
      eac_no_inf_arrivals_correspondence pR pL Hp.
    have Hstep := eac_step_at_correspondence pR pL 0 Lean.Nat_zero
      Hp (@Lean.eq_refl _ _).
    have Htarget : Lean.eq (eac_imported_step (O, O))
        (IF.Prod_mk_inst3 Lean.Nat Lean.Nat Lean.Nat_zero Lean.Nat_zero) :=
      @Lean.eq_refl _ _.
    have Heq := facts_step_eq_correspondence _ _ _ _ Hstep Htarget.
    exact (prop_to_sprop _ _ Heq
      (HR pR (sprop_to_prop _ _ Hsorted HsortedL)
        (sprop_to_prop _ _ Hnoinf HnoinfL))).
  - intro HL. apply strictly_inhabits. intros pR HsortedR HnoinfR.
    set (pL := eac_imported_prefix pR).
    have Hp : EacPrefixRel pR pL := @Lean.eq_refl _ _.
    have Hsorted := facts_prefix_truth_correspondence _ _
      eac_sorted_ltn_steps_correspondence pR pL Hp.
    have Hnoinf := facts_prefix_truth_correspondence _ _
      eac_no_inf_arrivals_correspondence pR pL Hp.
    have Hstep := eac_step_at_correspondence pR pL 0 Lean.Nat_zero
      Hp (@Lean.eq_refl _ _).
    have Htarget : Lean.eq (eac_imported_step (O, O))
        (IF.Prod_mk_inst3 Lean.Nat Lean.Nat Lean.Nat_zero Lean.Nat_zero) :=
      @Lean.eq_refl _ _.
    have Heq := facts_step_eq_correspondence _ _ _ _ Hstep Htarget.
    exact (sprop_to_prop _ _ Heq
      (HL pL (prop_to_sprop _ _ Hsorted HsortedR)
        (prop_to_sprop _ _ Hnoinf HnoinfR))).
Defined.

(** Ordered pair-list membership.  This is independent of either facts
    theorem and retains MathComp sequence multiplicity/order. *)
Definition facts_target_pair_mem (p : FactsStepL)
    (xs : IF.List_inst1 FactsStepL) : SProp :=
  IF.Membership_mem_inst3 FactsStepL (IF.List_inst1 FactsStepL)
    (IF.List_instMembership_inst1 FactsStepL) xs p.

Definition facts_pair_list_mem_transport (p : FactsStepL) xs ys :
    Lean.eq xs ys -> IF.List_Mem_inst1 FactsStepL p xs ->
    IF.List_Mem_inst1 FactsStepL p ys :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ zs return IF.List_Mem_inst1 FactsStepL p zs with
    | Lean.eq_refl => Hmem
    end.

Definition facts_pair_mem_head_of_eq (p q : FactsStepR)
    (ys : IF.List_inst1 FactsStepL) :
    Logic.eq p q ->
    IF.List_Mem_inst1 FactsStepL (eac_imported_step p)
      (IF.List_cons_inst1 FactsStepL (eac_imported_step q) ys) :=
  fun Hpq => match Hpq in Logic.eq _ z return
      IF.List_Mem_inst1 FactsStepL (eac_imported_step p)
        (IF.List_cons_inst1 FactsStepL (eac_imported_step z) ys) with
    | Logic.eq_refl => IF.List_Mem_head_inst1 FactsStepL
        (eac_imported_step p) ys
    end.

Fixpoint facts_pair_seq_mem_forward (p : FactsStepR) (xs : seq FactsStepR) :
    SubNatTruth (p \in xs) ->
    IF.List_Mem_inst1 FactsStepL (eac_imported_step p)
      (eac_imported_steps xs) :=
  match xs as zs return SubNatTruth (p \in zs) ->
      IF.List_Mem_inst1 FactsStepL (eac_imported_step p)
        (eac_imported_steps zs) with
  | [::] => sub_nat_false_elim _
  | q :: qs =>
      match @eqP _ p q as rr in reflect _ b return
        SubNatTruth (b || (p \in qs)) ->
        IF.List_Mem_inst1 FactsStepL (eac_imported_step p)
          (IF.List_cons_inst1 FactsStepL (eac_imported_step q)
            (eac_imported_steps qs)) with
      | ReflectT Hpq => fun _ =>
          facts_pair_mem_head_of_eq p q (eac_imported_steps qs) Hpq
      | ReflectF _ => fun H =>
          IF.List_Mem_tail_inst1 FactsStepL
            (eac_imported_step p) (eac_imported_step q)
            (eac_imported_steps qs)
            (facts_pair_seq_mem_forward p qs H)
      end
  end.

Definition facts_pair_mem_refl_truth (p : FactsStepR) ys :
    SubNatTruth (p \in eac_rocq_step (eac_imported_step p) :: ys).
Proof.
  rewrite (eac_step_rocq_roundtrip p) in_cons eqxx.
  exact sub_nat_truth_intro.
Defined.

Fixpoint facts_imported_pair_mem_decoded (p : FactsStepR)
    (xs : IF.List_inst1 FactsStepL)
    (H : IF.List_Mem_inst1 FactsStepL (eac_imported_step p) xs) :
    SubNatTruth (p \in eac_rocq_steps xs) :=
  match H with
  | IF.List_Mem_head_inst1 ys =>
      facts_pair_mem_refl_truth p (eac_rocq_steps ys)
  | IF.List_Mem_tail_inst1 q ys Htail =>
      eac_mem_tail_truth _ _ (facts_imported_pair_mem_decoded p ys Htail)
  end.

Definition facts_pair_mem_truth_transport (p : FactsStepR)
    (xs ys : seq FactsStepR) :
    Logic.eq xs ys -> SubNatTruth (p \in xs) ->
    SubNatTruth (p \in ys) :=
  fun H Htruth =>
    match H in Logic.eq _ zs return
      SubNatTruth (p \in xs) -> SubNatTruth (p \in zs) with
    | Logic.eq_refl => fun Ht => Ht
    end Htruth.

Definition facts_pair_membership_correspondence
    (pR : FactsStepR) (xsR : seq FactsStepR)
    (xsL : IF.List_inst1 FactsStepL)
    (Hxs : Lean.eq (eac_imported_steps xsR) xsL) :
    PropSPropRel (pR \in xsR)
      (facts_target_pair_mem (eac_imported_step pR) xsL).
Proof.
  constructor.
  - intro Hmem. unfold facts_target_pair_mem.
    apply (facts_pair_list_mem_transport (eac_imported_step pR) _ _ Hxs).
    apply facts_pair_seq_mem_forward.
    exact (sub_nat_prop_to_truth _ Hmem).
  - intro Hmem. apply interpret_strict.
    apply sub_nat_truth_to_strict_prop.
    apply (facts_pair_mem_truth_transport pR _ _
      (eac_steps_rocq_roundtrip xsR)).
    apply facts_imported_pair_mem_decoded.
    unfold facts_target_pair_mem in Hmem.
    exact (facts_pair_list_mem_transport (eac_imported_step pR) _ _
      (sub_imported_eq_sym _ _ Hxs) Hmem).
Defined.

Definition facts_pair_mem_element_transport (p q : FactsStepL) xs :
    Lean.eq p q -> IF.List_Mem_inst1 FactsStepL p xs ->
    IF.List_Mem_inst1 FactsStepL q xs :=
  fun Hpq Hmem =>
    match Hpq in Lean.eq _ z return IF.List_Mem_inst1 FactsStepL z xs with
    | Lean.eq_refl => Hmem
    end.

Definition facts_step_at_agrees_with_steps_of_certificate :
  PropSPropRel OF.statement_step_at_agrees_with_steps_of
    (forall pL : FactsPrefixL,
      Lean.eq (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sorted_ltn_steps pL) IF.Bool_true ->
      forall tL vL : Lean.Nat,
        facts_target_pair_mem (IF.Prod_mk_inst3 Lean.Nat Lean.Nat tL vL)
          (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_steps_of pL) ->
        Lean.eq
          (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_step_at pL tL)
          (IF.Prod_mk_inst3 Lean.Nat Lean.Nat tL vL)).
Proof.
  apply prop_sprop_rel_intro.
  - intros HR pL HsortedL tL vL HmemL.
    set (pR := eac_rocq_prefix pL).
    set (tR := sub_nat_to_rocq tL).
    set (vR := sub_nat_to_rocq vL).
    have Hp := eac_prefix_imported_roundtrip pL.
    have Ht := sub_nat_imported_roundtrip tL.
    have Hv := sub_nat_imported_roundtrip vL.
    have Hpair : Lean.eq (eac_imported_step (tR, vR))
        (IF.Prod_mk_inst3 Lean.Nat Lean.Nat tL vL) :=
      sub_imported_eq_congr2 (IF.Prod_mk_inst3 Lean.Nat Lean.Nat)
        _ _ _ _ Ht Hv.
    have Hsorted := facts_prefix_truth_correspondence _ _
      eac_sorted_ltn_steps_correspondence pR pL Hp.
    have Hsteps := eac_steps_of_correspondence pR pL Hp.
    have Hmem := facts_pair_membership_correspondence (tR, vR)
      (OfficialExtrapolatedArrivalCurve.steps_of pR)
      (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_steps_of pL)
      Hsteps.
    have HmemCanonical : facts_target_pair_mem (eac_imported_step (tR, vR))
        (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_steps_of pL) :=
      facts_pair_mem_element_transport _ _ _
        (sub_imported_eq_sym _ _ Hpair) HmemL.
    have Hstep := eac_step_at_correspondence pR pL tR tL Hp Ht.
    have Heq := facts_step_eq_correspondence _ _ _ _ Hstep Hpair.
    exact (prop_to_sprop _ _ Heq
      (HR pR (sprop_to_prop _ _ Hsorted HsortedL)
        tR vR (sprop_to_prop _ _ Hmem HmemCanonical))).
  - intro HL. apply strictly_inhabits.
    intros pR HsortedR tR vR HmemR.
    set (pL := eac_imported_prefix pR).
    set (tL := sub_nat_to_imported tR).
    set (vL := sub_nat_to_imported vR).
    have Hp : EacPrefixRel pR pL := @Lean.eq_refl _ _.
    have Ht : SubNatRel tR tL := @Lean.eq_refl _ _.
    have Hv : SubNatRel vR vL := @Lean.eq_refl _ _.
    have Hpair : Lean.eq (eac_imported_step (tR, vR))
        (IF.Prod_mk_inst3 Lean.Nat Lean.Nat tL vL) :=
      @Lean.eq_refl _ _.
    have Hsorted := facts_prefix_truth_correspondence _ _
      eac_sorted_ltn_steps_correspondence pR pL Hp.
    have Hsteps := eac_steps_of_correspondence pR pL Hp.
    have Hmem := facts_pair_membership_correspondence (tR, vR)
      (OfficialExtrapolatedArrivalCurve.steps_of pR)
      (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_steps_of pL)
      Hsteps.
    have HmemCanonical : facts_target_pair_mem (eac_imported_step (tR, vR))
        (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_steps_of pL) :=
      prop_to_sprop _ _ Hmem HmemR.
    have HmemTarget : facts_target_pair_mem
        (IF.Prod_mk_inst3 Lean.Nat Lean.Nat tL vL)
        (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_steps_of pL) :=
      facts_pair_mem_element_transport _ _ _ Hpair HmemCanonical.
    have Hstep := eac_step_at_correspondence pR pL tR tL Hp Ht.
    have Heq := facts_step_eq_correspondence _ _ _ _ Hstep Hpair.
    exact (sprop_to_prop _ _ Heq
      (HL pL (prop_to_sprop _ _ Hsorted HsortedR)
        tL vL HmemTarget)).
Defined.

Definition facts_exists_step_value_correspondence
    (pR : FactsPrefixR) (pL : FactsPrefixL)
    (nextR : nat) (nextL : Lean.Nat)
    (Hp : EacPrefixRel pR pL) (Hnext : SubNatRel nextR nextL) :
    PropSPropRel
      (exists vR : nat,
        (nextR, vR) \in OfficialExtrapolatedArrivalCurve.steps_of pR)
      (IF.Exists Lean.Nat (fun vL =>
        facts_target_pair_mem
          (IF.Prod_mk_inst3 Lean.Nat Lean.Nat nextL vL)
          (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_steps_of pL))).
Proof.
  have Hsteps := eac_steps_of_correspondence pR pL Hp.
  apply prop_sprop_rel_intro.
  - intros [vR HmemR].
    set (vL := sub_nat_to_imported vR).
    have Hv : SubNatRel vR vL := @Lean.eq_refl _ _.
    have Hpair : Lean.eq (eac_imported_step (nextR, vR))
        (IF.Prod_mk_inst3 Lean.Nat Lean.Nat nextL vL) :=
      sub_imported_eq_congr2 (IF.Prod_mk_inst3 Lean.Nat Lean.Nat)
        _ _ _ _ Hnext Hv.
    have Hmem := facts_pair_membership_correspondence (nextR, vR)
      (OfficialExtrapolatedArrivalCurve.steps_of pR)
      (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_steps_of pL)
      Hsteps.
    exact (IF.Exists_intro Lean.Nat _ vL
      (facts_pair_mem_element_transport _ _ _ Hpair
        (prop_to_sprop _ _ Hmem HmemR))).
  - intro Hex. destruct Hex as [vL HmemL].
    set (vR := sub_nat_to_rocq vL).
    have Hv := sub_nat_imported_roundtrip vL.
    have Hpair : Lean.eq (eac_imported_step (nextR, vR))
        (IF.Prod_mk_inst3 Lean.Nat Lean.Nat nextL vL) :=
      sub_imported_eq_congr2 (IF.Prod_mk_inst3 Lean.Nat Lean.Nat)
        _ _ _ _ Hnext Hv.
    have Hmem := facts_pair_membership_correspondence (nextR, vR)
      (OfficialExtrapolatedArrivalCurve.steps_of pR)
      (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_steps_of pL)
      Hsteps.
    have Hcanonical : facts_target_pair_mem (eac_imported_step (nextR, vR))
        (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_steps_of pL) :=
      facts_pair_mem_element_transport _ _ _
        (sub_imported_eq_sym _ _ Hpair) HmemL.
    apply strictly_inhabits. exists vR.
    exact (sprop_to_prop _ _ Hmem Hcanonical).
Defined.

Definition facts_target_next (tL : Lean.Nat) : Lean.Nat :=
  eac_imported_add tL (Lean.Nat_succ Lean.Nat_zero).

Definition facts_value_at_change_is_in_steps_of_certificate :
  PropSPropRel OF.statement_value_at_change_is_in_steps_of
    (forall pL : FactsPrefixL,
      Lean.eq (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sorted_leq_steps pL) IF.Bool_true ->
      Lean.eq (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_no_inf_arrivals pL) IF.Bool_true ->
      forall tL : Lean.Nat,
        IF.LT_lt_inst1 Lean.Nat IF.instLTNat
          (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_value_at pL tL)
          (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_value_at pL (facts_target_next tL)) ->
        IF.Exists Lean.Nat (fun vL =>
          facts_target_pair_mem
            (IF.Prod_mk_inst3 Lean.Nat Lean.Nat (facts_target_next tL) vL)
            (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_steps_of pL))).
Proof.
  apply prop_sprop_rel_intro.
  - intros HR pL HsortedL HnoinfL tL HltL.
    set (pR := eac_rocq_prefix pL).
    set (tR := sub_nat_to_rocq tL).
    have Hp := eac_prefix_imported_roundtrip pL.
    have Ht := sub_nat_imported_roundtrip tL.
    have Hone : SubNatRel 1%N (Lean.Nat_succ Lean.Nat_zero) :=
      @Lean.eq_refl _ _.
    have Hnext := eac_add_correspondence tR tL 1%N
      (Lean.Nat_succ Lean.Nat_zero) Ht Hone.
    have Hsorted := facts_prefix_truth_correspondence _ _
      eac_sorted_leq_steps_correspondence pR pL Hp.
    have Hnoinf := facts_prefix_truth_correspondence _ _
      eac_no_inf_arrivals_correspondence pR pL Hp.
    have Hv1 := eac_value_at_correspondence pR pL tR tL Hp Ht.
    have Hv2 := eac_value_at_correspondence pR pL (tR + 1) (facts_target_next tL) Hp Hnext.
    have Hlt := eac_lt_correspondence _ _ _ _ Hv1 Hv2.
    have Hexists := facts_exists_step_value_correspondence pR pL
      (tR + 1) (facts_target_next tL) Hp Hnext.
    exact (prop_to_sprop _ _ Hexists
      (HR pR (sprop_to_prop _ _ Hsorted HsortedL)
        (sprop_to_prop _ _ Hnoinf HnoinfL)
        tR (sprop_to_prop _ _ Hlt HltL))).
  - intro HL. apply strictly_inhabits.
    intros pR HsortedR HnoinfR tR HltR.
    set (pL := eac_imported_prefix pR).
    set (tL := sub_nat_to_imported tR).
    have Hp : EacPrefixRel pR pL := @Lean.eq_refl _ _.
    have Ht : SubNatRel tR tL := @Lean.eq_refl _ _.
    have Hone : SubNatRel 1%N (Lean.Nat_succ Lean.Nat_zero) :=
      @Lean.eq_refl _ _.
    have Hnext := eac_add_correspondence tR tL 1%N
      (Lean.Nat_succ Lean.Nat_zero) Ht Hone.
    have Hsorted := facts_prefix_truth_correspondence _ _
      eac_sorted_leq_steps_correspondence pR pL Hp.
    have Hnoinf := facts_prefix_truth_correspondence _ _
      eac_no_inf_arrivals_correspondence pR pL Hp.
    have Hv1 := eac_value_at_correspondence pR pL tR tL Hp Ht.
    have Hv2 := eac_value_at_correspondence pR pL (tR + 1) (facts_target_next tL) Hp Hnext.
    have Hlt := eac_lt_correspondence _ _ _ _ Hv1 Hv2.
    have Hexists := facts_exists_step_value_correspondence pR pL
      (tR + 1) (facts_target_next tL) Hp Hnext.
    exact (sprop_to_prop _ _ Hexists
      (HL pL (prop_to_sprop _ _ Hsorted HsortedR)
        (prop_to_sprop _ _ Hnoinf HnoinfR)
        tL (prop_to_sprop _ _ Hlt HltR))).
Defined.

Definition facts_or_correspondence (P Q : Prop) (PL QL : SProp)
    (HP : PropSPropRel P PL) (HQ : PropSPropRel Q QL) :
    PropSPropRel (P \/ Q) (Lean.Or PL QL).
Proof.
  apply prop_sprop_rel_intro.
  - intros [p|q].
    + exact (Lean.Or_inl PL QL (prop_to_sprop _ _ HP p)).
    + exact (Lean.Or_inr PL QL (prop_to_sprop _ _ HQ q)).
  - intro H. destruct H as [p|q].
    + exact (strictly_inhabits (or_introl _ (sprop_to_prop _ _ HP p))).
    + exact (strictly_inhabits (or_intror _ (sprop_to_prop _ _ HQ q))).
Defined.

Definition facts_nat_ne_correspondence aR aL bR bL
    (Ha : SubNatRel aR aL) (Hb : SubNatRel bR bL) :
    PropSPropRel (is_true (aR != bR)) (IF.Ne Lean.Nat aL bL).
Proof.
  have Heq := eac_eq_correspondence aR aL bR bL Ha Hb.
  apply prop_sprop_rel_intro.
  - intros Hneq HeqL.
    have HeqR := sprop_to_prop _ _ Heq HeqL.
    have HeqB : aR == bR. { apply/eqP. exact HeqR. }
    rewrite HeqB in Hneq.
    have Hfalse : Logic.False. { discriminate Hneq. }
    destruct Hfalse.
  - intro HneL. destruct (aR != bR) eqn:Hneq.
    + exact (strictly_inhabits (Logic.eq_refl true)).
    + have HeqB : aR == bR.
      { destruct (aR == bR) eqn:HeqVal; first reflexivity.
        cbn in Hneq. discriminate Hneq. }
      have HeqR : Logic.eq aR bR. { apply/eqP. exact HeqB. }
      have HeqL := prop_to_sprop _ _ Heq HeqR.
      exact (match HneL HeqL return
        StrictlyInhabited (is_true false) with end).
Defined.

Definition facts_target_div (pL : FactsPrefixL) (tL : Lean.Nat) : Lean.Nat :=
  eac_imported_div tL
    (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_horizon_of pL).

Definition facts_target_mod (pL : FactsPrefixL) (tL : Lean.Nat) : Lean.Nat :=
  eac_imported_mod tL
    (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_horizon_of pL).

Definition facts_change_target (pL : FactsPrefixL) (tL : Lean.Nat) : SProp :=
  Lean.Or
    (IF.LT_lt_inst1 Lean.Nat IF.instLTNat
      (facts_target_div pL tL)
      (facts_target_div pL (facts_target_next tL)))
    (Lean.And
      (Lean.eq (facts_target_div pL tL)
        (facts_target_div pL (facts_target_next tL)))
      (IF.LT_lt_inst1 Lean.Nat IF.instLTNat
        (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_value_at pL
          (facts_target_mod pL tL))
        (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_value_at pL
          (facts_target_mod pL (facts_target_next tL))))).

Definition facts_change_conclusion_correspondence
    (pR : FactsPrefixR) (pL : FactsPrefixL)
    (tR : nat) (tL : Lean.Nat)
    (Hp : EacPrefixRel pR pL) (Ht : SubNatRel tR tL) :
    PropSPropRel
      ((is_true (ltn
         (tR %/ OfficialExtrapolatedArrivalCurve.horizon_of pR)
         ((tR + 1) %/ OfficialExtrapolatedArrivalCurve.horizon_of pR))) \/
       ((tR %/ OfficialExtrapolatedArrivalCurve.horizon_of pR =
         (tR + 1) %/ OfficialExtrapolatedArrivalCurve.horizon_of pR) /\
        (is_true (ltn
          (OfficialExtrapolatedArrivalCurve.value_at pR
            (tR %% OfficialExtrapolatedArrivalCurve.horizon_of pR))
          (OfficialExtrapolatedArrivalCurve.value_at pR
            ((tR + 1) %% OfficialExtrapolatedArrivalCurve.horizon_of pR))))))
      (facts_change_target pL tL).
Proof.
  have Hone : SubNatRel 1%N (Lean.Nat_succ Lean.Nat_zero) :=
    @Lean.eq_refl _ _.
  have Hnext := eac_add_correspondence tR tL 1%N
    (Lean.Nat_succ Lean.Nat_zero) Ht Hone.
  have Hh := eac_horizon_of_correspondence pR pL Hp.
  have Hdiv1 := eac_div_correspondence tR tL _ _ Ht Hh.
  have Hdiv2 := eac_div_correspondence (tR + 1) (facts_target_next tL)
    _ _ Hnext Hh.
  have Hmod1 := eac_mod_correspondence tR tL _ _ Ht Hh.
  have Hmod2 := eac_mod_correspondence (tR + 1) (facts_target_next tL)
    _ _ Hnext Hh.
  have Hv1 := eac_value_at_correspondence pR pL _ _ Hp Hmod1.
  have Hv2 := eac_value_at_correspondence pR pL _ _ Hp Hmod2.
  have Hleft := eac_lt_correspondence _ _ _ _ Hdiv1 Hdiv2.
  have HrightEq := eac_eq_correspondence _ _ _ _ Hdiv1 Hdiv2.
  have HrightLt := eac_lt_correspondence _ _ _ _ Hv1 Hv2.
  exact (facts_or_correspondence _ _ _ _ Hleft
    (eac_and_correspondence _ _ _ _ HrightEq HrightLt)).
Defined.

Definition facts_extrapolated_arrival_curve_change_certificate :
  PropSPropRel OF.statement_extrapolated_arrival_curve_change
    (forall pL : FactsPrefixL,
      Lean.eq (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_positive_horizon pL) IF.Bool_true ->
      Lean.eq (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_sorted_leq_steps pL) IF.Bool_true ->
      forall tL : Lean.Nat,
        IF.Ne Lean.Nat
          (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_extrapolated_arrival_curve pL tL)
          (IF.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_extrapolated_arrival_curve pL (facts_target_next tL)) ->
        facts_change_target pL tL).
Proof.
  apply prop_sprop_rel_intro.
  - intros HR pL HpositiveL HsortedL tL HneL.
    set (pR := eac_rocq_prefix pL).
    set (tR := sub_nat_to_rocq tL).
    have Hp := eac_prefix_imported_roundtrip pL.
    have Ht := sub_nat_imported_roundtrip tL.
    have Hone : SubNatRel 1%N (Lean.Nat_succ Lean.Nat_zero) :=
      @Lean.eq_refl _ _.
    have Hnext := eac_add_correspondence tR tL 1%N
      (Lean.Nat_succ Lean.Nat_zero) Ht Hone.
    have Hpositive := facts_prefix_truth_correspondence _ _
      eac_positive_horizon_correspondence pR pL Hp.
    have Hsorted := facts_prefix_truth_correspondence _ _
      eac_sorted_leq_steps_correspondence pR pL Hp.
    have Hcurve1 := eac_extrapolated_arrival_curve_correspondence
      pR pL tR tL Hp Ht.
    have Hcurve2 := eac_extrapolated_arrival_curve_correspondence
      pR pL (tR + 1) (facts_target_next tL) Hp Hnext.
    have Hne := facts_nat_ne_correspondence _ _ _ _ Hcurve1 Hcurve2.
    have Hresult := facts_change_conclusion_correspondence pR pL tR tL Hp Ht.
    exact (prop_to_sprop _ _ Hresult
      (HR pR (sprop_to_prop _ _ Hpositive HpositiveL)
        (sprop_to_prop _ _ Hsorted HsortedL)
        tR (sprop_to_prop _ _ Hne HneL))).
  - intro HL. apply strictly_inhabits.
    intros pR HpositiveR HsortedR tR HneR.
    set (pL := eac_imported_prefix pR).
    set (tL := sub_nat_to_imported tR).
    have Hp : EacPrefixRel pR pL := @Lean.eq_refl _ _.
    have Ht : SubNatRel tR tL := @Lean.eq_refl _ _.
    have Hone : SubNatRel 1%N (Lean.Nat_succ Lean.Nat_zero) :=
      @Lean.eq_refl _ _.
    have Hnext := eac_add_correspondence tR tL 1%N
      (Lean.Nat_succ Lean.Nat_zero) Ht Hone.
    have Hpositive := facts_prefix_truth_correspondence _ _
      eac_positive_horizon_correspondence pR pL Hp.
    have Hsorted := facts_prefix_truth_correspondence _ _
      eac_sorted_leq_steps_correspondence pR pL Hp.
    have Hcurve1 := eac_extrapolated_arrival_curve_correspondence
      pR pL tR tL Hp Ht.
    have Hcurve2 := eac_extrapolated_arrival_curve_correspondence
      pR pL (tR + 1) (facts_target_next tL) Hp Hnext.
    have Hne := facts_nat_ne_correspondence _ _ _ _ Hcurve1 Hcurve2.
    have Hresult := facts_change_conclusion_correspondence pR pL tR tL Hp Ht.
    exact (sprop_to_prop _ _ Hresult
      (HL pL (prop_to_sprop _ _ Hpositive HpositiveR)
        (prop_to_sprop _ _ Hsorted HsortedR)
        tL (prop_to_sprop _ _ Hne HneR))).
Defined.

Print Assumptions facts_ltn_steps_is_transitive_certificate.
Print Assumptions facts_leq_steps_is_reflexive_certificate.
Print Assumptions facts_leq_steps_is_transitive_certificate.
Print Assumptions facts_sorted_ltn_implies_sorted_leq_certificate.
Print Assumptions facts_value_at_monotone_certificate.
Print Assumptions facts_extrapolated_arrival_curve_is_monotone_certificate.
Print Assumptions facts_step_at_zero_certificate.
Print Assumptions facts_step_at_agrees_with_steps_of_certificate.
Print Assumptions facts_value_at_change_is_in_steps_of_certificate.
Print Assumptions facts_extrapolated_arrival_curve_change_certificate.
