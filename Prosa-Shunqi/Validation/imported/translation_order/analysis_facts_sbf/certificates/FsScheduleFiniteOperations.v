(* Re-bound copy of accepted imported/translation_order/analysis_facts_behavior_supply/certificates/FsScheduleFiniteOperations.v for the analysis/facts/SBF artifact;
   only the imported module name differs. *)
(** GENERATED ARTIFACT-LOCAL INSTANTIATION.
    source: /Users/shunqiwang/CityuHK/Research/Lean/TranslationProof/Prosa-Shunqi/Validation/certificates/behavior_schedule/ScheduleFiniteOperations.v
    source-sha256: 3ce4ecae129fe7a807498e674c943bd228712a1289987da90266af36d5d87525
    imported-artifact-sha256: 4c8b1853fa6065b80a5df21916ea90ab306ca01194b1a71aeec4ffa1653adcc3 *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From prosa Require Import behavior.schedule.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSbfFacts ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence FsScheduleBaseAdapter.

(** Operation-level correspondence for the actual compiled Schedule
    artifact.  In particular, finite sums are reduced to ordered list folds
    without importing Lean's theorem proof dependency graph. *)

Definition sch_target_zero : Lean.Nat :=
  ImportedSbfFacts.OfNat_ofNat_inst1 Lean.Nat Lean.Nat_zero
    (ImportedSbfFacts.instOfNatNat Lean.Nat_zero).

Definition sch_target_add (a b : Lean.Nat) : Lean.Nat :=
  ImportedSbfFacts.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedSbfFacts.instHAdd_inst1 Lean.Nat
      ImportedSbfFacts.instAddNat) a b.

Definition sch_target_list_sum
    (xs : ImportedSbfFacts.List_inst1 Lean.Nat) : Lean.Nat :=
  ImportedSbfFacts.List_sum_inst1 Lean.Nat
    ImportedSbfFacts.instAddNat
    (ImportedSbfFacts.MulZeroClass_toZero_inst1 Lean.Nat
      ImportedSbfFacts.Nat_instMulZeroClass) xs.

Fixpoint sch_nat_list_to_imported (xs : seq nat) :
    ImportedSbfFacts.List_inst1 Lean.Nat :=
  match xs with
  | [::] => ImportedSbfFacts.List_nil_inst1 Lean.Nat
  | x :: tail => ImportedSbfFacts.List_cons_inst1 Lean.Nat
      (sub_nat_to_imported x) (sch_nat_list_to_imported tail)
  end.

Definition SchNatListRel (xsR : seq nat)
    (xsL : ImportedSbfFacts.List_inst1 Lean.Nat) : SProp :=
  Lean.eq (sch_nat_list_to_imported xsR) xsL.

Lemma sch_target_add_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR + bR) (sch_target_add aL bL).
Proof. exact (sub_add_correspondence aR aL bR bL). Qed.

Fixpoint sch_list_sum_canonical (xs : seq nat) :
  SubNatRel (foldr addn O xs)
    (sch_target_list_sum (sch_nat_list_to_imported xs)).
Proof.
  destruct xs as [|x xs].
  - exact (sub_nat_rel_canonical O).
  - exact (sch_target_add_related x (sub_nat_to_imported x)
      (foldr addn O xs)
      (sch_target_list_sum (sch_nat_list_to_imported xs))
      (sub_nat_rel_canonical x) (sch_list_sum_canonical xs)).
Defined.

Lemma sch_list_sum_related (xsR : seq nat)
    (xsL : ImportedSbfFacts.List_inst1 Lean.Nat) :
  SchNatListRel xsR xsL ->
  SubNatRel (foldr addn O xsR) (sch_target_list_sum xsL).
Proof.
  intro Hxs. unfold SchNatListRel in Hxs.
  exact (sub_imported_eq_trans _ _ _ (sch_list_sum_canonical xsR)
    (sub_imported_eq_congr sch_target_list_sum _ _ Hxs)).
Qed.

Definition SchCoreEnumerationRel (CoreR : finType) (CoreL : Type)
    (toL : CoreR -> CoreL)
    (enumL : ImportedSbfFacts.List CoreL) : SProp :=
  Lean.eq (sch_list_to_imported (map toL (enum CoreR))) enumL.

Definition SchCoreNatFunRel (CoreR : finType) (CoreL : Type)
    (toL : CoreR -> CoreL) (fR : CoreR -> nat)
    (fL : CoreL -> Lean.Nat) : SProp :=
  forall cR, SubNatRel (fR cR) (fL (toL cR)).

Fixpoint sch_map_core_values_canonical
    (CoreR : finType) (CoreL : Type) (toL : CoreR -> CoreL)
    (fR : CoreR -> nat) (fL : CoreL -> Lean.Nat)
    (Hf : SchCoreNatFunRel CoreR CoreL toL fR fL)
    (xs : seq CoreR) :
  Lean.eq (sch_nat_list_to_imported (map fR xs))
    (ImportedSbfFacts.List_map_inst2 CoreL Lean.Nat fL
      (sch_list_to_imported (map toL xs))).
Proof.
  destruct xs as [|x xs].
  - exact (@Lean.eq_refl _ _).
  - cbn [map sch_nat_list_to_imported sch_list_to_imported].
    exact (sub_imported_eq_congr2
      (ImportedSbfFacts.List_cons_inst1 Lean.Nat) _ _ _ _
      (Hf x) (sch_map_core_values_canonical CoreR CoreL toL
        fR fL Hf xs)).
Defined.

Lemma sch_map_core_values_related
    (CoreR : finType) (CoreL : Type) (toL : CoreR -> CoreL)
    (fR : CoreR -> nat) (fL : CoreL -> Lean.Nat)
    (enumL : ImportedSbfFacts.List CoreL) :
  SchCoreNatFunRel CoreR CoreL toL fR fL ->
  SchCoreEnumerationRel CoreR CoreL toL enumL ->
  SchNatListRel (map fR (enum CoreR))
    (ImportedSbfFacts.List_map_inst2 CoreL Lean.Nat fL enumL).
Proof.
  intros Hf Henum. unfold SchNatListRel, SchCoreEnumerationRel in *.
  exact (sub_imported_eq_trans _ _ _
    (sch_map_core_values_canonical CoreR CoreL toL fR fL Hf
      (enum CoreR))
    (sub_imported_eq_congr
      (ImportedSbfFacts.List_map_inst2 CoreL Lean.Nat fL) _ _ Henum)).
Qed.

Lemma sch_mathcomp_big_seq_as_fold (CoreR : Type)
    (xs : seq CoreR) (fR : CoreR -> nat) :
  Logic.eq (\sum_(c <- xs) fR c)
    (foldr addn O (map fR xs)).
Proof.
  elim: xs => [|x xs IH].
  - rewrite big_nil. reflexivity.
  - rewrite big_cons. cbn [map foldr]. now rewrite IH.
Qed.

Lemma sch_mathcomp_big_enum_as_fold (CoreR : finType)
    (fR : CoreR -> nat) :
  Logic.eq (\sum_(c : CoreR) fR c)
    (foldr addn O (map fR (enum CoreR))).
Proof.
  rewrite -big_enum.
  exact (sch_mathcomp_big_seq_as_fold CoreR (enum CoreR) fR).
Qed.

Lemma sch_finite_sum_related
    (CoreR : finType) (CoreL : Type) (toL : CoreR -> CoreL)
    (fR : CoreR -> nat) (fL : CoreL -> Lean.Nat)
    (enumL : ImportedSbfFacts.List CoreL) :
  SchCoreNatFunRel CoreR CoreL toL fR fL ->
  SchCoreEnumerationRel CoreR CoreL toL enumL ->
  SubNatRel (\sum_(c : CoreR) fR c)
    (sch_target_list_sum
      (ImportedSbfFacts.List_map_inst2 CoreL Lean.Nat fL enumL)).
Proof.
  intros Hf Henum.
  rewrite (sch_mathcomp_big_enum_as_fold CoreR fR).
  apply sch_list_sum_related.
  exact (sch_map_core_values_related CoreR CoreL toL fR fL enumL
    Hf Henum).
Qed.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN sch_list_sum_related". exact I. Qed.
Print Assumptions sch_list_sum_related.
Goal Logic.True.
Proof. idtac "AUDIT_END sch_list_sum_related". exact I. Qed.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN sch_finite_sum_related". exact I. Qed.
Print Assumptions sch_finite_sum_related.
Goal Logic.True.
Proof. idtac "AUDIT_END sch_finite_sum_related". exact I. Qed.
