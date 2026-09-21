From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedListLast.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  ListLastCertificate ListRemCertificate
  ListBatch2Certificate ListBatch3Operations.
From prosa Require Import GeneratedListLastSource.

(** Operation-level correspondence for the range/iota cluster.  These
    lemmas inspect only imported computation equations from the frozen
    production artifact; none depends on a target theorem in this batch. *)

Definition l4_target_range_prime (start len : Lean.Nat) :
    ImportedListLast.List_inst1 Lean.Nat :=
  ImportedListLast.List_range' start len ll_target_one.

Definition l4_target_index_iota (a b : Lean.Nat) :
    ImportedListLast.List_inst1 Lean.Nat :=
  ImportedListLast.Prosa_Util_List_index_iota a b.

Definition l4_target_range (a b : Lean.Nat) :
    ImportedListLast.List_inst1 Lean.Nat :=
  ImportedListLast.Prosa_Util_List_range a b.

Lemma l4_local_sub_zero (a : Lean.Nat) :
  Lean.eq (ll_target_sub a ll_target_zero) a.
Proof. exact (@Lean.eq_refl Lean.Nat a). Qed.

Lemma l4_local_sub_succ (a b : Lean.Nat) :
  Lean.eq (ll_target_sub a (Lean.Nat_succ b))
    (ImportedListLast.Nat_pred (ll_target_sub a b)).
Proof.
  exact (@Lean.eq_refl Lean.Nat
    (ImportedListLast.Nat_pred (ll_target_sub a b))).
Qed.

Definition l4_local_pred_canonical (n : nat) :
  Lean.eq (ImportedListLast.Nat_pred (sub_nat_to_imported n))
    (sub_nat_to_imported (Nat.pred n)) :=
  match n return
    Lean.eq (ImportedListLast.Nat_pred (sub_nat_to_imported n))
      (sub_nat_to_imported (Nat.pred n))
  with
  | O => @Lean.eq_refl Lean.Nat Lean.Nat_zero
  | S n' => @Lean.eq_refl Lean.Nat (sub_nat_to_imported n')
  end.

(** A local computational characterization of truncated subtraction keeps
    this List batch tied only to the actual [ImportedListLast] Nat body.  It
    deliberately avoids importing the independent [ImportedNat] artifact. *)
Fixpoint l4_rocq_iterated_pred (a b : nat) : nat :=
  match b with
  | O => a
  | S b' => Nat.pred (l4_rocq_iterated_pred a b')
  end.

Lemma l4_rocq_iterated_pred_is_subn (a b : nat) :
  Logic.eq (l4_rocq_iterated_pred a b) (a - b).
Proof.
  revert a. induction b as [|b IH]; intro a;
    cbn [l4_rocq_iterated_pred].
  - rewrite subn0. reflexivity.
  - rewrite (IH a). exact (Logic.eq_sym (subnS a b)).
Qed.

Lemma l4_local_sub_iterated_pred (a b : nat) :
  Lean.eq
    (ll_target_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (l4_rocq_iterated_pred a b)).
Proof.
  induction b as [|b IH].
  - exact (l4_local_sub_zero (sub_nat_to_imported a)).
  - exact (sub_imported_eq_trans _ _ _
      (l4_local_sub_succ _ _)
      (sub_imported_eq_trans _ _ _
        (sub_imported_eq_congr ImportedListLast.Nat_pred _ _ IH)
        (l4_local_pred_canonical (l4_rocq_iterated_pred a b)))).
Qed.

Lemma l4_local_sub_canonical (a b : nat) :
  Lean.eq
    (ll_target_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (a - b)).
Proof.
  exact (sub_imported_eq_trans _ _ _
    (l4_local_sub_iterated_pred a b)
    (coq_eq_to_imported_eq _ _
      (f_equal sub_nat_to_imported
        (l4_rocq_iterated_pred_is_subn a b)))).
Qed.

Lemma l4_local_sub_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR - bR) (ll_target_sub aL bL).
Proof.
  intros Ha Hb. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (l4_local_sub_canonical aR bR))
    (sub_imported_eq_congr2 ll_target_sub _ _ _ _ Ha Hb)).
Qed.

Lemma l4_iota_canonical (m n : nat) :
  LlListRel (iota m n)
    (l4_target_range_prime (sub_nat_to_imported m)
      (sub_nat_to_imported n)).
Proof.
  revert m. induction n as [|n IH]; intro m.
  - cbn [iota ll_to_imported].
    exact (sub_imported_eq_sym _ _
      (ImportedListLast.Prosa_Validation_ListLastInterface_generic_range_prime_zero
        (sub_nat_to_imported m))).
  - cbn [iota ll_to_imported].
    refine (sub_imported_eq_trans _ _ _
      (sub_imported_eq_congr
        (ImportedListLast.List_cons_inst1 Lean.Nat
          (sub_nat_to_imported m)) _ _ (IH m.+1)) _).
    exact (sub_imported_eq_sym _ _
      (ImportedListLast.Prosa_Validation_ListLastInterface_generic_range_prime_succ
        (sub_nat_to_imported m) (sub_nat_to_imported n))).
Qed.

Lemma l4_iota_related mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  LlListRel (iota mR nR) (l4_target_range_prime mL nL).
Proof.
  intros Hm Hn. unfold LlListRel.
  exact (sub_imported_eq_trans _ _ _ (l4_iota_canonical mR nR)
    (sub_imported_eq_congr2 l4_target_range_prime _ _ _ _ Hm Hn)).
Qed.

Lemma l4_index_iota_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  LlListRel (index_iota aR bR) (l4_target_index_iota aL bL).
Proof.
  intros Ha Hb. rewrite /index_iota.
  have Hsub := l4_local_sub_related bR bL aR aL Hb Ha.
  have Hiota := l4_iota_related aR aL (bR - aR)
    (ll_target_sub bL aL) Ha Hsub.
  unfold LlListRel in Hiota |- *.
  exact (sub_imported_eq_trans _ _ _ Hiota
    (sub_imported_eq_sym _ _
      (ImportedListLast.Prosa_Validation_ListLastInterface_production_index_iota_eq
        aL bL))).
Qed.

Lemma l4_range_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  LlListRel (GeneratedListLastSource.range aR bR)
    (l4_target_range aL bL).
Proof.
  intros Ha Hb. unfold GeneratedListLastSource.range.
  have Hb1 := lr_add_related bR bL 1 ll_target_one Hb lr_one_related.
  rewrite addn1 in Hb1.
  have Hidx := l4_index_iota_related aR aL bR.+1
    (lr_target_add bL ll_target_one) Ha Hb1.
  unfold LlListRel in Hidx |- *.
  exact (sub_imported_eq_trans _ _ _ Hidx
    (sub_imported_eq_sym _ _
      (ImportedListLast.Prosa_Validation_ListLastInterface_production_range_eq
        aL bL))).
Qed.

(** Boolean equality and membership observations used as filter predicates. *)
Definition l4_target_decide_eq (x y : Lean.Nat) : ImportedListLast.Bool :=
  ImportedListLast.Decidable_decide (Lean.eq x y)
    (ImportedListLast.instDecidableEqNat x y).

Lemma l4_decide_eq_related xR xL yR yL :
  SubNatRel xR xL -> SubNatRel yR yL ->
  LlBoolRel (xR == yR) (l4_target_decide_eq xL yL).
Proof.
  intros Hx Hy. apply lr_eqb_decide_from_eq_rel.
  exact (sub_nat_eq_correspondence xR xL yR yL Hx Hy).
Qed.

Definition l4_target_mem_decidable (x : Lean.Nat)
    (xs : ImportedListLast.List_inst1 Lean.Nat) :
    ImportedListLast.Decidable (ll_target_mem x xs) :=
  ImportedListLast.List_instDecidableMemOfLawfulBEq_inst1 Lean.Nat
    (ImportedListLast.instBEqOfDecidableEq_inst1 Lean.Nat
      ImportedListLast.instDecidableEqNat)
    ImportedListLast.Nat_instLawfulBEq x xs.

Definition l4_target_decide_mem (x : Lean.Nat)
    (xs : ImportedListLast.List_inst1 Lean.Nat) : ImportedListLast.Bool :=
  ImportedListLast.Decidable_decide (ll_target_mem x xs)
    (l4_target_mem_decidable x xs).

Lemma l4_decide_mem_related xR xL xsR xsL :
  SubNatRel xR xL -> LlListRel xsR xsL ->
  LlBoolRel (xR \in xsR) (l4_target_decide_mem xL xsL).
Proof.
  intros Hx Hxs. apply lr_decide_bool_correspondence.
  exact (ll_membership_correspondence xR xL xsR xsL Hx Hxs).
Qed.

(** Nat-specialized actual [rem_all].  lean4export monomorphizes the [List]
    carrier in the final theorem type, so this bridge is intentionally
    separate from the previously certified universe-polymorphic operation. *)
Definition l4_target_rem_all (x : Lean.Nat)
    (xs : ImportedListLast.List_inst1 Lean.Nat) :
    ImportedListLast.List_inst1 Lean.Nat :=
  ImportedListLast.Prosa_Util_List_rem_all_inst1 Lean.Nat
    ImportedListLast.instDecidableEqNat x xs.

Lemma l4_target_rem_all_nil (x : Lean.Nat) :
  Lean.eq (l4_target_rem_all x
    (ImportedListLast.List_nil_inst1 Lean.Nat))
    (ImportedListLast.List_nil_inst1 Lean.Nat).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma l4_target_rem_all_cons (x a : Lean.Nat)
    (xs : ImportedListLast.List_inst1 Lean.Nat) :
  Lean.eq
    (l4_target_rem_all x
      (ImportedListLast.List_cons_inst1 Lean.Nat a xs))
    (ImportedListLast.ite (ImportedListLast.List_inst1 Lean.Nat)
      (Lean.eq a x) (ImportedListLast.instDecidableEqNat a x)
      (l4_target_rem_all x xs)
      (ImportedListLast.List_cons_inst1 Lean.Nat a
        (l4_target_rem_all x xs))).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma l4_rem_all_canonical (x : nat) (xs : seq nat) :
  LlListRel (GeneratedListLastSource.rem_all x xs)
    (l4_target_rem_all (sub_nat_to_imported x) (ll_to_imported xs)).
Proof.
  unfold LlListRel. induction xs as [|a xs IH].
  - exact (sub_imported_eq_sym _ _
      (l4_target_rem_all_nil (sub_nat_to_imported x))).
  - cbn [GeneratedListLastSource.rem_all ll_to_imported].
    have Hstep := l4_target_rem_all_cons (sub_nat_to_imported x)
      (sub_nat_to_imported a) (ll_to_imported xs).
    destruct (@eqP _ a x) as [Heq | Hneq].
    + subst a.
      have Hite := lb_imported_ite_true
        (Lean.eq (sub_nat_to_imported x) (sub_nat_to_imported x))
        (ImportedListLast.instDecidableEqNat
          (sub_nat_to_imported x) (sub_nat_to_imported x))
        (@Lean.eq_refl Lean.Nat (sub_nat_to_imported x))
        (l4_target_rem_all (sub_nat_to_imported x) (ll_to_imported xs))
        (ImportedListLast.List_cons_inst1 Lean.Nat (sub_nat_to_imported x)
          (l4_target_rem_all (sub_nat_to_imported x) (ll_to_imported xs))).
      exact (sub_imported_eq_trans _ _ _ IH
        (sub_imported_eq_sym _ _
          (sub_imported_eq_trans _ _ _ Hstep Hite))).
    +
      have Hnot : ImportedListLast.Not
          (Lean.eq (sub_nat_to_imported a) (sub_nat_to_imported x)) :=
        fun HeqL => ll_coq_false_to_target
          (Hneq (Logic.eq_trans (Logic.eq_sym (sub_nat_rocq_roundtrip a))
            (Logic.eq_trans
              (f_equal sub_nat_to_rocq
                (imported_eq_to_coq_eq _ _ HeqL))
              (sub_nat_rocq_roundtrip x)))).
      have Hite := lb_imported_ite_false
        (Lean.eq (sub_nat_to_imported a) (sub_nat_to_imported x))
        (ImportedListLast.instDecidableEqNat
          (sub_nat_to_imported a) (sub_nat_to_imported x)) Hnot
        (l4_target_rem_all (sub_nat_to_imported x) (ll_to_imported xs))
        (ImportedListLast.List_cons_inst1 Lean.Nat (sub_nat_to_imported a)
          (l4_target_rem_all (sub_nat_to_imported x) (ll_to_imported xs))).
      have Hcons := sub_imported_eq_congr
        (ImportedListLast.List_cons_inst1 Lean.Nat
          (sub_nat_to_imported a)) _ _ IH.
      exact (sub_imported_eq_trans _ _ _ Hcons
        (sub_imported_eq_sym _ _
          (sub_imported_eq_trans _ _ _ Hstep Hite))).
Qed.

Lemma l4_rem_all_related xR xL xsR xsL :
  SubNatRel xR xL -> LlListRel xsR xsL ->
  LlListRel (GeneratedListLastSource.rem_all xR xsR)
    (l4_target_rem_all xL xsL).
Proof.
  intros Hx Hxs. unfold LlListRel.
  exact (sub_imported_eq_trans _ _ _ (l4_rem_all_canonical xR xsR)
    (sub_imported_eq_congr2 l4_target_rem_all _ _ _ _ Hx Hxs)).
Qed.

Print Assumptions l4_iota_related.
Print Assumptions l4_index_iota_related.
Print Assumptions l4_range_related.
Print Assumptions l4_decide_eq_related.
Print Assumptions l4_decide_mem_related.
Print Assumptions l4_rem_all_related.
