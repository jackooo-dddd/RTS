From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq bigop.
From prosa Require Import analysis.facts.model.task_cost.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTaskCost ImportedSubadditivity.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  TaskCostBaseAdapter TaskCostClasses.

(** Artifact-local instantiation of the accepted Schedule finite-fold
    pattern.  The MathComp sequence sum and the actual Lean List.map/sum
    remain in their original order and count duplicates. *)

Definition tc_target_add (a b : Lean.Nat) : Lean.Nat :=
  ImportedTaskCost.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedTaskCost.instHAdd_inst1 Lean.Nat
      ImportedTaskCost.instAddNat) a b.

Definition tc_target_list_sum
    (xs : ImportedTaskCost.List_inst1 Lean.Nat) : Lean.Nat :=
  ImportedTaskCost.List_sum_inst1 Lean.Nat
    ImportedTaskCost.instAddNat
    (ImportedTaskCost.MulZeroClass_toZero_inst1 Lean.Nat
      ImportedTaskCost.Nat_instMulZeroClass) xs.

Fixpoint tc_nat_list_to_imported (xs : seq nat) :
    ImportedTaskCost.List_inst1 Lean.Nat :=
  match xs with
  | [::] => ImportedTaskCost.List_nil_inst1 Lean.Nat
  | x :: tail => ImportedTaskCost.List_cons_inst1 Lean.Nat
      (sub_nat_to_imported x) (tc_nat_list_to_imported tail)
  end.

Definition TcNatListRel (xsR : seq nat)
    (xsL : ImportedTaskCost.List_inst1 Lean.Nat) : SProp :=
  Lean.eq (tc_nat_list_to_imported xsR) xsL.

Lemma tc_target_add_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR + bR) (tc_target_add aL bL).
Proof. exact (sub_add_correspondence aR aL bR bL). Qed.

Fixpoint tc_list_sum_canonical (xs : seq nat) :
  SubNatRel (foldr addn O xs)
    (tc_target_list_sum (tc_nat_list_to_imported xs)).
Proof.
  destruct xs as [|x xs].
  - exact (sub_nat_rel_canonical O).
  - exact (tc_target_add_related x (sub_nat_to_imported x)
      (foldr addn O xs)
      (tc_target_list_sum (tc_nat_list_to_imported xs))
      (sub_nat_rel_canonical x) (tc_list_sum_canonical xs)).
Defined.

Lemma tc_list_sum_related (xsR : seq nat)
    (xsL : ImportedTaskCost.List_inst1 Lean.Nat) :
  TcNatListRel xsR xsL ->
  SubNatRel (foldr addn O xsR) (tc_target_list_sum xsL).
Proof.
  intro Hxs. unfold TcNatListRel in Hxs.
  exact (sub_imported_eq_trans _ _ _ (tc_list_sum_canonical xsR)
    (sub_imported_eq_congr tc_target_list_sum _ _ Hxs)).
Qed.

Fixpoint tc_map_values_canonical (T : Type)
    (fR : T -> nat) (fL : T -> Lean.Nat)
    (Hf : forall x, SubNatRel (fR x) (fL x)) (xs : seq T) :
  Lean.eq (tc_nat_list_to_imported (map fR xs))
    (ImportedTaskCost.List_map_inst2 T Lean.Nat fL
      (tc_list_to_imported xs)).
Proof.
  destruct xs as [|x xs].
  - exact (@Lean.eq_refl _ _).
  - cbn [map tc_nat_list_to_imported tc_list_to_imported].
    exact (sub_imported_eq_congr2
      (ImportedTaskCost.List_cons_inst1 Lean.Nat) _ _ _ _
      (Hf x) (tc_map_values_canonical T fR fL Hf xs)).
Defined.

Lemma tc_map_values_related (T : Type)
    (fR : T -> nat) (fL : T -> Lean.Nat)
    (xsR : seq T) (xsL : ImportedTaskCost.List T) :
  (forall x, SubNatRel (fR x) (fL x)) ->
  TcListRel xsR xsL ->
  TcNatListRel (map fR xsR)
    (ImportedTaskCost.List_map_inst2 T Lean.Nat fL xsL).
Proof.
  intros Hf Hxs. unfold TcListRel, TcNatListRel in *.
  exact (sub_imported_eq_trans _ _ _
    (tc_map_values_canonical T fR fL Hf xsR)
    (sub_imported_eq_congr
      (ImportedTaskCost.List_map_inst2 T Lean.Nat fL) _ _ Hxs)).
Qed.

Lemma tc_mathcomp_big_seq_as_fold (T : Type)
    (xs : seq T) (f : T -> nat) :
  Logic.eq (\sum_(x <- xs) f x) (foldr addn O (map f xs)).
Proof.
  elim: xs => [|x xs IH].
  - rewrite big_nil. reflexivity.
  - rewrite big_cons. cbn [map foldr]. now rewrite IH.
Qed.

Lemma tc_big_seq_sum_related (T : Type)
    (fR : T -> nat) (fL : T -> Lean.Nat)
    (xsR : seq T) (xsL : ImportedTaskCost.List T) :
  (forall x, SubNatRel (fR x) (fL x)) ->
  TcListRel xsR xsL ->
  SubNatRel (\sum_(x <- xsR) fR x)
    (tc_target_list_sum
      (ImportedTaskCost.List_map_inst2 T Lean.Nat fL xsL)).
Proof.
  intros Hf Hxs.
  rewrite (tc_mathcomp_big_seq_as_fold T xsR fR).
  apply tc_list_sum_related.
  exact (tc_map_values_related T fR fL xsR xsL Hf Hxs).
Qed.

Fixpoint tc_length_canonical (T : Type) (xs : seq T) :
  SubNatRel (size xs)
    (ImportedTaskCost.List_length T (tc_list_to_imported xs)).
Proof.
  destruct xs as [|x xs].
  - exact (sub_nat_rel_canonical O).
  - cbn [size tc_list_to_imported ImportedTaskCost.List_length].
    exact (sub_imported_eq_congr Lean.Nat_succ _ _
      (tc_length_canonical T xs)).
Defined.

Lemma tc_length_related (T : Type)
    (xsR : seq T) (xsL : ImportedTaskCost.List T) :
  TcListRel xsR xsL ->
  SubNatRel (size xsR) (ImportedTaskCost.List_length T xsL).
Proof.
  intro Hxs. unfold TcListRel in Hxs.
  exact (sub_imported_eq_trans _ _ _ (tc_length_canonical T xsR)
    (sub_imported_eq_congr (ImportedTaskCost.List_length T) _ _ Hxs)).
Qed.

Print Assumptions tc_big_seq_sum_related.
Print Assumptions tc_length_related.
