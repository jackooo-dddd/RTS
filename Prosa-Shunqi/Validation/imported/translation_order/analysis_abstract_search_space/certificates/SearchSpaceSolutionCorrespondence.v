From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From prosa Require Import analysis.abstract.search_space.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSearchSpace.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  SearchSpaceBaseAdapter SearchSpaceDefinitionsCorrespondence
  SearchSpaceLogicalOperations.

Section SolutionCorrespondence.
  Variables (bR : nat) (bL : Lean.Nat).
  Variables (ibfR : nat -> nat -> nat)
    (ibfL : Lean.Nat -> Lean.Nat -> Lean.Nat).
  Variables (aspR fspR aR : nat) (aspL fspL aL : Lean.Nat).
  Hypothesis Hb : SubNatRel bR bL.
  Hypothesis Hibf : SearchIBFRel ibfR ibfL.
  Hypothesis Hasp : SubNatRel aspR aspL.
  Hypothesis Hfsp : SubNatRel fspR fspL.
  Hypothesis Ha : SubNatRel aR aL.

  Lemma ss_solution_conclusion_correspondence :
    PropSPropRel
      (exists fR : nat,
        Logic.eq (addn aspR fspR) (addn aR fR) /\
        is_true (leq fR fspR) /\
        is_true (leq (ibfR aR (addn aR fR)) (addn aR fR)))
      (ImportedSearchSpace.Exists Lean.Nat
        (fun fL => Lean.And
          (Lean.eq (sub_imported_add aspL fspL)
            (sub_imported_add aL fL))
          (Lean.And
            (ImportedSearchSpace.LE_le_inst1 Lean.Nat
              ImportedSearchSpace.instLENat fL fspL)
            (ImportedSearchSpace.LE_le_inst1 Lean.Nat
              ImportedSearchSpace.instLENat
              (ibfL aL (sub_imported_add aL fL))
              (sub_imported_add aL fL))))).
  Proof.
    apply ss_exists_nat_correspondence.
    intros fR fL Hf.
    have HsumRep := sub_add_correspondence aspR aspL fspR fspL Hasp Hfsp.
    have HsumA := sub_add_correspondence aR aL fR fL Ha Hf.
    apply ss_and_correspondence.
    - exact (sub_nat_eq_correspondence _ _ _ _ HsumRep HsumA).
    - apply ss_and_correspondence.
      + exact (sub_nat_le_correspondence fR fL fspR fspL Hf Hfsp).
      + exact (sub_nat_le_correspondence
          (ibfR aR (addn aR fR)) (ibfL aL (sub_imported_add aL fL))
          (addn aR fR) (sub_imported_add aL fL)
          (Hibf _ _ _ _ Ha HsumA) HsumA).
  Qed.

  Lemma ss_solution_statement_correspondence :
    PropSPropRel
      (is_true (ltn (addn aspR fspR) bR) ->
       is_true (leq (ibfR aspR (addn aspR fspR)) (addn aspR fspR)) ->
       is_true (andb (leq aspR aR) (leq aR (addn aspR fspR))) ->
       @prosa.analysis.abstract.search_space.are_equivalent_at_values_less_than
         _ (ibfR aR) (ibfR aspR) bR ->
       exists fR : nat,
         Logic.eq (addn aspR fspR) (addn aR fR) /\
         is_true (leq fR fspR) /\
         is_true (leq (ibfR aR (addn aR fR)) (addn aR fR)))
      (ImportedSearchSpace.LT_lt_inst1 Lean.Nat
         ImportedSearchSpace.instLTNat
         (sub_imported_add aspL fspL) bL ->
       ImportedSearchSpace.LE_le_inst1 Lean.Nat
         ImportedSearchSpace.instLENat
         (ibfL aspL (sub_imported_add aspL fspL))
         (sub_imported_add aspL fspL) ->
       Lean.And
         (ImportedSearchSpace.LE_le_inst1 Lean.Nat
           ImportedSearchSpace.instLENat aspL aL)
         (ImportedSearchSpace.LE_le_inst1 Lean.Nat
           ImportedSearchSpace.instLENat aL
           (sub_imported_add aspL fspL)) ->
       ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_are_equivalent_at_values_less_than
         Lean.Nat ImportedSearchSpace.instDecidableEqNat
         (ibfL aL) (ibfL aspL) bL ->
       ImportedSearchSpace.Exists Lean.Nat
         (fun fL => Lean.And
           (Lean.eq (sub_imported_add aspL fspL)
             (sub_imported_add aL fL))
           (Lean.And
             (ImportedSearchSpace.LE_le_inst1 Lean.Nat
               ImportedSearchSpace.instLENat fL fspL)
             (ImportedSearchSpace.LE_le_inst1 Lean.Nat
               ImportedSearchSpace.instLENat
               (ibfL aL (sub_imported_add aL fL))
               (sub_imported_add aL fL))))).
  Proof.
    have HsumRep := sub_add_correspondence aspR aspL fspR fspL Hasp Hfsp.
    apply ss_imp_correspondence.
    - exact (sub_nat_lt_correspondence _ _ _ _ HsumRep Hb).
    - apply ss_imp_correspondence.
      + exact (sub_nat_le_correspondence
          (ibfR aspR (addn aspR fspR))
          (ibfL aspL (sub_imported_add aspL fspL))
          (addn aspR fspR) (sub_imported_add aspL fspL)
          (Hibf _ _ _ _ Hasp HsumRep) HsumRep).
      + apply ss_imp_correspondence.
        * apply ss_andb_correspondence.
          -- exact (sub_nat_le_correspondence aspR aspL aR aL Hasp Ha).
          -- exact (sub_nat_le_correspondence aR aL
               (addn aspR fspR) (sub_imported_add aspL fspL)
               Ha HsumRep).
        * apply ss_imp_correspondence.
          -- exact (ss_nat_equivalent_correspondence
               (ibfR aR) (ibfR aspR) (ibfL aL) (ibfL aspL)
               bR bL
               (fun xR xL Hx => Hibf _ _ _ _ Ha Hx)
               (fun xR xL Hx => Hibf _ _ _ _ Hasp Hx) Hb).
          -- exact ss_solution_conclusion_correspondence.
  Qed.
End SolutionCorrespondence.

Print Assumptions ss_solution_conclusion_correspondence.
Print Assumptions ss_solution_statement_correspondence.
