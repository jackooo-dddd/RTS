From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From prosa Require Import analysis.abstract.search_space.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSearchSpace.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  SearchSpaceBaseAdapter SearchSpaceDefinitionsCorrespondence
  SearchSpaceLogicalOperations.

Section RepresentativeCorrespondence.
  Variables (bR : nat) (bL : Lean.Nat).
  Variables (ibfR : nat -> nat -> nat)
    (ibfL : Lean.Nat -> Lean.Nat -> Lean.Nat).
  Variables (aR : nat) (aL : Lean.Nat).
  Hypothesis Hb : SubNatRel bR bL.
  Hypothesis Hibf : SearchIBFRel ibfR ibfL.
  Hypothesis Ha : SubNatRel aR aL.

  Lemma ss_representative_conclusion_correspondence :
    PropSPropRel
      (exists aspR : nat,
        is_true (leq aspR aR) /\
        @prosa.analysis.abstract.search_space.are_equivalent_at_values_less_than
          _ (ibfR aR) (ibfR aspR) bR /\
        prosa.analysis.abstract.search_space.is_in_search_space bR ibfR aspR)
      (ImportedSearchSpace.Exists Lean.Nat
        (fun aspL => Lean.And
          (ImportedSearchSpace.LE_le_inst1 Lean.Nat
            ImportedSearchSpace.instLENat aspL aL)
          (Lean.And
            (ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_are_equivalent_at_values_less_than
              Lean.Nat ImportedSearchSpace.instDecidableEqNat
              (ibfL aL) (ibfL aspL) bL)
            (ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_is_in_search_space
              bL ibfL aspL)))).
  Proof.
    apply ss_exists_nat_correspondence.
    intros aspR aspL Hasp.
    apply ss_and_correspondence.
    - exact (sub_nat_le_correspondence aspR aspL aR aL Hasp Ha).
    - apply ss_and_correspondence.
      + exact (ss_nat_equivalent_correspondence
          (ibfR aR) (ibfR aspR) (ibfL aL) (ibfL aspL)
          bR bL
          (fun xR xL Hx => Hibf _ _ _ _ Ha Hx)
          (fun xR xL Hx => Hibf _ _ _ _ Hasp Hx) Hb).
      + exact (ss_search_space_correspondence
          bR bL ibfR ibfL aspR aspL Hb Hibf Hasp).
  Qed.

  Lemma ss_representative_statement_correspondence :
    PropSPropRel
      (is_true (ltn aR bR) ->
        exists aspR : nat,
          is_true (leq aspR aR) /\
          @prosa.analysis.abstract.search_space.are_equivalent_at_values_less_than
            _ (ibfR aR) (ibfR aspR) bR /\
          prosa.analysis.abstract.search_space.is_in_search_space bR ibfR aspR)
      (ImportedSearchSpace.LT_lt_inst1 Lean.Nat
        ImportedSearchSpace.instLTNat aL bL ->
        ImportedSearchSpace.Exists Lean.Nat
          (fun aspL => Lean.And
            (ImportedSearchSpace.LE_le_inst1 Lean.Nat
              ImportedSearchSpace.instLENat aspL aL)
            (Lean.And
              (ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_are_equivalent_at_values_less_than
                Lean.Nat ImportedSearchSpace.instDecidableEqNat
                (ibfL aL) (ibfL aspL) bL)
              (ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_is_in_search_space
                bL ibfL aspL)))).
  Proof.
    apply ss_imp_correspondence.
    - exact (sub_nat_lt_correspondence aR aL bR bL Ha Hb).
    - exact ss_representative_conclusion_correspondence.
  Qed.
End RepresentativeCorrespondence.

Print Assumptions ss_representative_conclusion_correspondence.
Print Assumptions ss_representative_statement_correspondence.
