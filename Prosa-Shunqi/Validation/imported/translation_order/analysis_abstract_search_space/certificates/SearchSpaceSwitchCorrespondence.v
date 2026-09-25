From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From prosa Require Import analysis.abstract.search_space.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSearchSpace.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  SearchSpaceBaseAdapter SearchSpaceDefinitionsCorrespondence
  SearchSpaceLogicalOperations.

Section SwitchCorrespondence.
  Variables (bR : nat) (bL : Lean.Nat).
  Variables (ibf1R ibf2R : nat -> nat -> nat)
    (ibf1L ibf2L : Lean.Nat -> Lean.Nat -> Lean.Nat).
  Hypothesis Hb : SubNatRel bR bL.
  Hypothesis Hibf1 : SearchIBFRel ibf1R ibf1L.
  Hypothesis Hibf2 : SearchIBFRel ibf2R ibf2L.

  Lemma ss_ibf_equal_below_correspondence :
    PropSPropRel
      (forall aR dR : nat,
        is_true (ltn aR bR) ->
        Logic.eq (ibf1R aR dR) (ibf2R aR dR))
      (forall aL dL : Lean.Nat,
        ImportedSearchSpace.LT_lt_inst1 Lean.Nat
          ImportedSearchSpace.instLTNat aL bL ->
        Lean.eq (ibf1L aL dL) (ibf2L aL dL)).
  Proof.
    apply ss_forall_nat_correspondence.
    intros aR aL Ha.
    apply ss_forall_nat_correspondence.
    intros dR dL Hd.
    apply ss_imp_correspondence.
    - exact (sub_nat_lt_correspondence aR aL bR bL Ha Hb).
    - exact (sub_nat_eq_correspondence _ _ _ _
        (Hibf1 _ _ _ _ Ha Hd) (Hibf2 _ _ _ _ Ha Hd)).
  Qed.

  Lemma ss_switch_at_correspondence aR aL :
    SubNatRel aR aL ->
    PropSPropRel
      ((forall a d : nat,
          is_true (ltn a bR) ->
          Logic.eq (ibf1R a d) (ibf2R a d)) ->
       prosa.analysis.abstract.search_space.is_in_search_space bR ibf1R aR ->
       prosa.analysis.abstract.search_space.is_in_search_space bR ibf2R aR)
      ((forall a d : Lean.Nat,
          ImportedSearchSpace.LT_lt_inst1 Lean.Nat
            ImportedSearchSpace.instLTNat a bL ->
          Lean.eq (ibf1L a d) (ibf2L a d)) ->
       ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_is_in_search_space
         bL ibf1L aL ->
       ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_is_in_search_space
         bL ibf2L aL).
  Proof.
    intro Ha.
    apply ss_imp_correspondence.
    - exact ss_ibf_equal_below_correspondence.
    - apply ss_imp_correspondence.
      + exact (ss_search_space_correspondence
          bR bL ibf1R ibf1L aR aL Hb Hibf1 Ha).
      + exact (ss_search_space_correspondence
          bR bL ibf2R ibf2L aR aL Hb Hibf2 Ha).
  Qed.

  Lemma ss_switch_forall_A_correspondence :
    PropSPropRel
      (forall aR : nat,
        (forall a d : nat,
          is_true (ltn a bR) ->
          Logic.eq (ibf1R a d) (ibf2R a d)) ->
        prosa.analysis.abstract.search_space.is_in_search_space bR ibf1R aR ->
        prosa.analysis.abstract.search_space.is_in_search_space bR ibf2R aR)
      (forall aL : Lean.Nat,
        (forall a d : Lean.Nat,
          ImportedSearchSpace.LT_lt_inst1 Lean.Nat
            ImportedSearchSpace.instLTNat a bL ->
          Lean.eq (ibf1L a d) (ibf2L a d)) ->
        ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_is_in_search_space
          bL ibf1L aL ->
        ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_is_in_search_space
          bL ibf2L aL).
  Proof.
    apply ss_forall_nat_correspondence.
    intros aR aL Ha.
    exact (ss_switch_at_correspondence aR aL Ha).
  Qed.

  Lemma ss_switch_statement_correspondence :
    PropSPropRel
      ((forall a d : nat,
          is_true (ltn a bR) ->
          Logic.eq (ibf1R a d) (ibf2R a d)) ->
       forall aR : nat,
         prosa.analysis.abstract.search_space.is_in_search_space bR ibf1R aR ->
         prosa.analysis.abstract.search_space.is_in_search_space bR ibf2R aR)
      ((forall a d : Lean.Nat,
          ImportedSearchSpace.LT_lt_inst1 Lean.Nat
            ImportedSearchSpace.instLTNat a bL ->
          Lean.eq (ibf1L a d) (ibf2L a d)) ->
       forall aL : Lean.Nat,
         ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_is_in_search_space
           bL ibf1L aL ->
         ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_is_in_search_space
           bL ibf2L aL).
  Proof.
    apply ss_imp_correspondence.
    - exact ss_ibf_equal_below_correspondence.
    - apply ss_forall_nat_correspondence.
      intros aR aL Ha.
      apply ss_imp_correspondence.
      + exact (ss_search_space_correspondence
          bR bL ibf1R ibf1L aR aL Hb Hibf1 Ha).
      + exact (ss_search_space_correspondence
          bR bL ibf2R ibf2L aR aL Hb Hibf2 Ha).
  Qed.
End SwitchCorrespondence.

Print Assumptions ss_ibf_equal_below_correspondence.
Print Assumptions ss_switch_at_correspondence.
Print Assumptions ss_switch_forall_A_correspondence.
Print Assumptions ss_switch_statement_correspondence.
