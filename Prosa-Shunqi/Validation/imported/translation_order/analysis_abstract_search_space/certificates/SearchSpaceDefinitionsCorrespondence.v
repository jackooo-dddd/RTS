From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From prosa Require Import analysis.abstract.search_space.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSearchSpace.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  SearchSpaceBaseAdapter.

Lemma ss_range_intro (a b : nat) :
  is_true (ltn O a) -> is_true (ltn a b) ->
  is_true (andb (ltn O a) (ltn a b)).
Proof. move=> Ha Hb. apply/andP. split; assumption. Qed.

Lemma ss_range_elim (a b : nat) :
  is_true (andb (ltn O a) (ltn a b)) ->
  is_true (ltn O a) /\ is_true (ltn a b).
Proof. move=> /andP [Ha Hb]. split; assumption. Qed.

Lemma ss_value_eq_correspondence (T : Type)
    (aR aL bR bL : T) :
  Lean.eq aR aL -> Lean.eq bR bL ->
  PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof.
  intros Ha Hb. apply prop_sprop_rel_intro.
  - intro Heq. exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _ Ha)
      (sub_imported_eq_trans _ _ _
        (coq_eq_to_imported_eq _ _ Heq) Hb)).
  - intro Heq. apply strictly_inhabits.
    exact (imported_eq_to_coq_eq _ _
      (sub_imported_eq_trans _ _ _ Ha
        (sub_imported_eq_trans _ _ _ Heq
          (sub_imported_eq_sym _ _ Hb)))).
Qed.

Lemma ss_value_ne_correspondence (T : Type)
    (aR aL bR bL : T) :
  Lean.eq aR aL -> Lean.eq bR bL ->
  PropSPropRel (aR <> bR) (ImportedSearchSpace.Ne T aL bL).
Proof.
  intros Ha Hb.
  have Heq := ss_value_eq_correspondence T aR aL bR bL Ha Hb.
  apply prop_sprop_rel_intro.
  - intros Hne HtargetEq.
    exact (match Hne (sprop_to_prop _ _ Heq HtargetEq) with end).
  - intro HtargetNe. apply strictly_inhabits. intro HsourceEq.
    have HtargetEq := prop_to_sprop _ _ Heq HsourceEq.
    exact (interpret_strict Logic.False
      (match HtargetNe HtargetEq with end)).
Qed.

Lemma ss_nat_ne_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (aR <> bR) (ImportedSearchSpace.Ne Lean.Nat aL bL).
Proof.
  intros Ha Hb.
  have Heq := sub_nat_eq_correspondence aR aL bR bL Ha Hb.
  apply prop_sprop_rel_intro.
  - intros Hne HtargetEq.
    exact (match Hne (sprop_to_prop _ _ Heq HtargetEq) with end).
  - intro HtargetNe. apply strictly_inhabits. intro HsourceEq.
    have HtargetEq := prop_to_sprop _ _ Heq HsourceEq.
    exact (interpret_strict Logic.False
      (match HtargetNe HtargetEq with end)).
Qed.

Lemma ss_nat_equivalent_correspondence
    (f1R f2R : nat -> nat) (f1L f2L : Lean.Nat -> Lean.Nat)
    bR bL :
  SubNatFunRel f1R f1L -> SubNatFunRel f2R f2L ->
  SubNatRel bR bL ->
  PropSPropRel
    (@prosa.analysis.abstract.search_space.are_equivalent_at_values_less_than
      _ f1R f2R bR)
    (ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_are_equivalent_at_values_less_than
      Lean.Nat ImportedSearchSpace.instDecidableEqNat f1L f2L bL).
Proof.
  intros Hf1 Hf2 Hb.
  unfold prosa.analysis.abstract.search_space.are_equivalent_at_values_less_than.
  cbn [ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_are_equivalent_at_values_less_than].
  apply prop_sprop_rel_intro.
  - intros Hsource xL HboundL.
    pose (xR := sub_nat_to_rocq xL).
    have Hx : SubNatRel xR xL := sub_nat_rel_surjective xL.
    have Hbound := sub_nat_lt_correspondence xR xL bR bL Hx Hb.
    have HboundR := sprop_to_prop _ _ Hbound HboundL.
    exact (prop_to_sprop _ _
      (sub_nat_eq_correspondence _ _ _ _
        (Hf1 xR xL Hx) (Hf2 xR xL Hx))
      (Hsource xR HboundR)).
  - intro Htarget. apply strictly_inhabits. intros xR HboundR.
    pose (xL := sub_nat_to_imported xR).
    have Hx : SubNatRel xR xL := sub_nat_rel_canonical xR.
    have Hbound := sub_nat_lt_correspondence xR xL bR bL Hx Hb.
    exact (sprop_to_prop _ _
      (sub_nat_eq_correspondence _ _ _ _
        (Hf1 xR xL Hx) (Hf2 xR xL Hx))
      (Htarget xL (prop_to_sprop _ _ Hbound HboundR))).
Qed.

Lemma ss_nat_not_equivalent_correspondence
    (f1R f2R : nat -> nat) (f1L f2L : Lean.Nat -> Lean.Nat)
    bR bL :
  SubNatFunRel f1R f1L -> SubNatFunRel f2R f2L ->
  SubNatRel bR bL ->
  PropSPropRel
    (@prosa.analysis.abstract.search_space.are_not_equivalent_at_values_less_than
      _ f1R f2R bR)
    (ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_are_not_equivalent_at_values_less_than
      Lean.Nat ImportedSearchSpace.instDecidableEqNat f1L f2L bL).
Proof.
  intros Hf1 Hf2 Hb.
  unfold prosa.analysis.abstract.search_space.are_not_equivalent_at_values_less_than.
  cbn [ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_are_not_equivalent_at_values_less_than].
  apply prop_sprop_rel_intro.
  - intros [xR [HboundR HneR]].
    pose (xL := sub_nat_to_imported xR).
    have Hx : SubNatRel xR xL := sub_nat_rel_canonical xR.
    have Hbound := sub_nat_lt_correspondence xR xL bR bL Hx Hb.
    have Hne := ss_nat_ne_correspondence _ _ _ _
      (Hf1 xR xL Hx) (Hf2 xR xL Hx).
    apply (ImportedSearchSpace.Exists_intro _ _ xL).
    exact (Lean.And_intro _ _
      (prop_to_sprop _ _ Hbound HboundR)
      (prop_to_sprop _ _ Hne HneR)).
  - intro Htarget.
    destruct Htarget as [xL Hpair].
    pose (xR := sub_nat_to_rocq xL).
    have Hx : SubNatRel xR xL := sub_nat_rel_surjective xL.
    have Hbound := sub_nat_lt_correspondence xR xL bR bL Hx Hb.
    have Hne := ss_nat_ne_correspondence _ _ _ _
      (Hf1 xR xL Hx) (Hf2 xR xL Hx).
    apply strictly_inhabits. exists xR. split.
    + exact (sprop_to_prop _ _ Hbound (ImportedSearchSpace.And_left _ _ Hpair)).
    + exact (sprop_to_prop _ _ Hne (ImportedSearchSpace.And_right _ _ Hpair)).
Qed.

Lemma ss_equivalent_correspondence (T : eqType)
    (f1R f2R : nat -> T) (f1L f2L : Lean.Nat -> T)
    bR bL :
  SearchFunRel T f1R f1L -> SearchFunRel T f2R f2L ->
  SubNatRel bR bL ->
  PropSPropRel
    (@prosa.analysis.abstract.search_space.are_equivalent_at_values_less_than
      T f1R f2R bR)
    (ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_are_equivalent_at_values_less_than
      T (ss_decidable_eq T) f1L f2L bL).
Proof.
  intros Hf1 Hf2 Hb.
  unfold prosa.analysis.abstract.search_space.are_equivalent_at_values_less_than.
  cbn [ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_are_equivalent_at_values_less_than].
  apply prop_sprop_rel_intro.
  - intros Hsource xL HboundL.
    pose (xR := sub_nat_to_rocq xL).
    have Hx : SubNatRel xR xL := sub_nat_rel_surjective xL.
    have Hbound := sub_nat_lt_correspondence xR xL bR bL Hx Hb.
    have HboundR := sprop_to_prop _ _ Hbound HboundL.
    have HeqR := Hsource xR HboundR.
    exact (prop_to_sprop _ _
      (ss_value_eq_correspondence T _ _ _ _
        (Hf1 xR xL Hx) (Hf2 xR xL Hx)) HeqR).
  - intro Htarget. apply strictly_inhabits. intros xR HboundR.
    pose (xL := sub_nat_to_imported xR).
    have Hx : SubNatRel xR xL := sub_nat_rel_canonical xR.
    have Hbound := sub_nat_lt_correspondence xR xL bR bL Hx Hb.
    have HboundL := prop_to_sprop _ _ Hbound HboundR.
    exact (sprop_to_prop _ _
      (ss_value_eq_correspondence T _ _ _ _
        (Hf1 xR xL Hx) (Hf2 xR xL Hx))
      (Htarget xL HboundL)).
Qed.

Lemma ss_not_equivalent_correspondence (T : eqType)
    (f1R f2R : nat -> T) (f1L f2L : Lean.Nat -> T)
    bR bL :
  SearchFunRel T f1R f1L -> SearchFunRel T f2R f2L ->
  SubNatRel bR bL ->
  PropSPropRel
    (@prosa.analysis.abstract.search_space.are_not_equivalent_at_values_less_than
      T f1R f2R bR)
    (ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_are_not_equivalent_at_values_less_than
      T (ss_decidable_eq T) f1L f2L bL).
Proof.
  intros Hf1 Hf2 Hb.
  unfold prosa.analysis.abstract.search_space.are_not_equivalent_at_values_less_than.
  cbn [ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_are_not_equivalent_at_values_less_than].
  apply prop_sprop_rel_intro.
  - intros [xR [HboundR HneR]].
    pose (xL := sub_nat_to_imported xR).
    have Hx : SubNatRel xR xL := sub_nat_rel_canonical xR.
    have Hbound := sub_nat_lt_correspondence xR xL bR bL Hx Hb.
    have Hne := ss_value_ne_correspondence T _ _ _ _
      (Hf1 xR xL Hx) (Hf2 xR xL Hx).
    apply (ImportedSearchSpace.Exists_intro _ _ xL).
    exact (Lean.And_intro _ _
      (prop_to_sprop _ _ Hbound HboundR)
      (prop_to_sprop _ _ Hne HneR)).
  - intro Htarget.
    destruct Htarget as [xL Hpair].
    pose (xR := sub_nat_to_rocq xL).
    have Hx : SubNatRel xR xL := sub_nat_rel_surjective xL.
    have Hbound := sub_nat_lt_correspondence xR xL bR bL Hx Hb.
    have Hne := ss_value_ne_correspondence T _ _ _ _
      (Hf1 xR xL Hx) (Hf2 xR xL Hx).
    apply strictly_inhabits. exists xR. split.
    + exact (sprop_to_prop _ _ Hbound (ImportedSearchSpace.And_left _ _ Hpair)).
    + exact (sprop_to_prop _ _ Hne (ImportedSearchSpace.And_right _ _ Hpair)).
Qed.

Lemma ss_search_space_correspondence bR bL
    (ibfR : nat -> nat -> nat)
    (ibfL : Lean.Nat -> Lean.Nat -> Lean.Nat)
    aR aL :
  SubNatRel bR bL -> SearchIBFRel ibfR ibfL -> SubNatRel aR aL ->
  PropSPropRel
    (prosa.analysis.abstract.search_space.is_in_search_space bR ibfR aR)
    (ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_is_in_search_space
      bL ibfL aL).
Proof.
  intros Hb Hibf Ha.
  unfold prosa.analysis.abstract.search_space.is_in_search_space.
  cbn [ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_is_in_search_space].
  have Hzero : SubNatRel 0 Lean.Nat_zero := sub_nat_rel_canonical 0.
  have Hprev := ss_target_sub_one_related aR aL Ha.
  have HnotEq := ss_nat_not_equivalent_correspondence
    (ibfR (aR - 1)) (ibfR aR)
    (ibfL (ss_target_sub aL ss_target_one)) (ibfL aL)
    bR bL
    (fun xR xL Hx => Hibf _ _ _ _ Hprev Hx)
    (fun xR xL Hx => Hibf _ _ _ _ Ha Hx) Hb.
  have Hpos := sub_nat_lt_correspondence 0 Lean.Nat_zero aR aL Hzero Ha.
  have Hbound := sub_nat_lt_correspondence aR aL bR bL Ha Hb.
  have HeqZero := sub_nat_eq_correspondence aR aL 0 Lean.Nat_zero Ha Hzero.
  apply prop_sprop_rel_intro.
  - intros [H0 | [HrangeR HnotEqR]].
    + exact (Lean.Or_inl _ _ (prop_to_sprop _ _ HeqZero H0)).
    + destruct (ss_range_elim aR bR HrangeR) as [HposR HboundR].
      exact (Lean.Or_inr _ _
        (Lean.And_intro _ _ (prop_to_sprop _ _ Hpos HposR)
          (Lean.And_intro _ _ (prop_to_sprop _ _ Hbound HboundR)
            (prop_to_sprop _ _ HnotEq HnotEqR)))).
  - intro Htarget.
    destruct Htarget as [H0L | Hrest].
    + apply strictly_inhabits. left.
      exact (sprop_to_prop _ _ HeqZero H0L).
    + have HposR := sprop_to_prop _ _ Hpos
        (ImportedSearchSpace.And_left _ _ Hrest).
      have HboundR := sprop_to_prop _ _ Hbound
        (ImportedSearchSpace.And_left _ _ (ImportedSearchSpace.And_right _ _ Hrest)).
      have HnotEqR := sprop_to_prop _ _ HnotEq
        (ImportedSearchSpace.And_right _ _ (ImportedSearchSpace.And_right _ _ Hrest)).
      apply strictly_inhabits. right. split.
      * exact (ss_range_intro aR bR HposR HboundR).
      * exact HnotEqR.
Qed.

Print Assumptions ss_equivalent_correspondence.
Print Assumptions ss_not_equivalent_correspondence.
Print Assumptions ss_search_space_correspondence.
