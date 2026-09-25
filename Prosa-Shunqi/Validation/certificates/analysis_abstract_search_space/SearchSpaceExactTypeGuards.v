From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSearchSpace.

Definition ss_guard_add (a b : Lean.Nat) : Lean.Nat :=
  ImportedSearchSpace.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedSearchSpace.instHAdd_inst1 Lean.Nat ImportedSearchSpace.instAddNat)
    a b.

Definition ss_guard_sub_one (a : Lean.Nat) : Lean.Nat :=
  ImportedSearchSpace.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedSearchSpace.instHSub_inst1 Lean.Nat ImportedSearchSpace.instSubNat)
    a (ImportedSearchSpace.OfNat_ofNat_inst1 Lean.Nat 1
      (ImportedSearchSpace.instOfNatNat 1)).

Definition ss_target_equivalent_type_guard (T : Type)
    (d : ImportedSearchSpace.DecidableEq T)
    (f1 f2 : Lean.Nat -> T) (B : Lean.Nat)
    (H : ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_are_equivalent_at_values_less_than
      T d f1 f2 B) :
  forall x : Lean.Nat,
    ImportedSearchSpace.LT_lt_inst1 Lean.Nat
      ImportedSearchSpace.instLTNat x B ->
    Lean.eq (f1 x) (f2 x) :=
  H.

Definition ss_target_not_equivalent_type_guard (T : Type)
    (d : ImportedSearchSpace.DecidableEq T)
    (f1 f2 : Lean.Nat -> T) (B : Lean.Nat)
    (H : ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_are_not_equivalent_at_values_less_than
      T d f1 f2 B) :
  ImportedSearchSpace.Exists Lean.Nat
    (fun x => Lean.And
      (ImportedSearchSpace.LT_lt_inst1 Lean.Nat
        ImportedSearchSpace.instLTNat x B)
      (ImportedSearchSpace.Ne T (f1 x) (f2 x))) :=
  H.

Definition ss_target_search_space_type_guard (B : Lean.Nat)
    (ibf : Lean.Nat -> Lean.Nat -> Lean.Nat) (A : Lean.Nat)
    (H : ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_is_in_search_space
      B ibf A) :
  Lean.Or (Lean.eq A Lean.Nat_zero)
    (Lean.And
      (ImportedSearchSpace.LT_lt_inst1 Lean.Nat
        ImportedSearchSpace.instLTNat Lean.Nat_zero A)
      (Lean.And
        (ImportedSearchSpace.LT_lt_inst1 Lean.Nat
          ImportedSearchSpace.instLTNat A B)
        (ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_are_not_equivalent_at_values_less_than
          Lean.Nat ImportedSearchSpace.instDecidableEqNat
          (ibf (ss_guard_sub_one A)) (ibf A) B))) :=
  H.

Definition ss_target_representative_type_guard (B : Lean.Nat)
    (ibf : Lean.Nat -> Lean.Nat -> Lean.Nat) (A : Lean.Nat)
    (Hlt : ImportedSearchSpace.LT_lt_inst1 Lean.Nat
      ImportedSearchSpace.instLTNat A B) :
  ImportedSearchSpace.Exists Lean.Nat
    (fun asp => Lean.And
      (ImportedSearchSpace.LE_le_inst1 Lean.Nat
        ImportedSearchSpace.instLENat asp A)
      (Lean.And
        (ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_are_equivalent_at_values_less_than
          Lean.Nat ImportedSearchSpace.instDecidableEqNat
          (ibf A) (ibf asp) B)
        (ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_is_in_search_space
          B ibf asp))) :=
  ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_representative_exists
    B ibf A Hlt.

Definition ss_target_solution_type_guard (B : Lean.Nat)
    (ibf : Lean.Nat -> Lean.Nat -> Lean.Nat)
    (asp fsp : Lean.Nat)
    (Hless : ImportedSearchSpace.LT_lt_inst1 Lean.Nat
      ImportedSearchSpace.instLTNat (ss_guard_add asp fsp) B)
    (Hfix : ImportedSearchSpace.LE_le_inst1 Lean.Nat
      ImportedSearchSpace.instLENat
      (ibf asp (ss_guard_add asp fsp)) (ss_guard_add asp fsp))
    (A : Lean.Nat)
    (Hbounds : Lean.And
      (ImportedSearchSpace.LE_le_inst1 Lean.Nat
        ImportedSearchSpace.instLENat asp A)
      (ImportedSearchSpace.LE_le_inst1 Lean.Nat
        ImportedSearchSpace.instLENat A (ss_guard_add asp fsp)))
    (Hequiv :
      ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_are_equivalent_at_values_less_than
        Lean.Nat ImportedSearchSpace.instDecidableEqNat
        (ibf A) (ibf asp) B) :
  ImportedSearchSpace.Exists Lean.Nat
    (fun f => Lean.And
      (Lean.eq (ss_guard_add asp fsp) (ss_guard_add A f))
      (Lean.And
        (ImportedSearchSpace.LE_le_inst1 Lean.Nat
          ImportedSearchSpace.instLENat f fsp)
        (ImportedSearchSpace.LE_le_inst1 Lean.Nat
          ImportedSearchSpace.instLENat
          (ibf A (ss_guard_add A f)) (ss_guard_add A f)))) :=
  ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_solution_for_A_exists
    B ibf asp fsp Hless Hfix A Hbounds Hequiv.

Definition ss_target_switch_type_guard (B : Lean.Nat)
    (ibf1 ibf2 : Lean.Nat -> Lean.Nat -> Lean.Nat)
    (Heq : forall A d : Lean.Nat,
      ImportedSearchSpace.LT_lt_inst1 Lean.Nat
        ImportedSearchSpace.instLTNat A B ->
      Lean.eq (ibf1 A d) (ibf2 A d))
    (A : Lean.Nat)
    (Hspace : ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_is_in_search_space
      B ibf1 A) :
  ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_is_in_search_space
    B ibf2 A :=
  ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_search_space_switch_IBF
    B ibf1 ibf2 Heq A Hspace.

Check ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_are_equivalent_at_values_less_than.
Check ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_are_not_equivalent_at_values_less_than.
Check ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_is_in_search_space.
Check ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_representative_exists.
Check ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_solution_for_A_exists.
Check ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_search_space_switch_IBF.

Print Assumptions ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_representative_exists.
Print Assumptions ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_solution_for_A_exists.
Print Assumptions ImportedSearchSpace.Prosa_Analysis_Abstract_SearchSpace_search_space_switch_IBF.
