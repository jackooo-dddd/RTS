From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedScheduleChange ImportedSubadditivity.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  ScheduleChangeBaseAdapter.

(** Ordered Nat-list representation, including duplicate positions. *)
Fixpoint sc_nat_list_to_imported (xs : seq nat) :
    ImportedScheduleChange.List_inst1 Lean.Nat :=
  match xs with
  | [::] => ImportedScheduleChange.List_nil_inst1 Lean.Nat
  | x :: tail => ImportedScheduleChange.List_cons_inst1 Lean.Nat
      (sub_nat_to_imported x) (sc_nat_list_to_imported tail)
  end.

Fixpoint sc_nat_list_to_source
    (xs : ImportedScheduleChange.List_inst1 Lean.Nat) : seq nat :=
  match xs with
  | ImportedScheduleChange.List_nil_inst1 => [::]
  | ImportedScheduleChange.List_cons_inst1 x tail =>
      sub_nat_to_rocq x :: sc_nat_list_to_source tail
  end.

Definition ScNatListRel (xsR : seq nat)
    (xsL : ImportedScheduleChange.List_inst1 Lean.Nat) : SProp :=
  Lean.eq (sc_nat_list_to_imported xsR) xsL.

Definition sc_nat_list_cons_congr (x y : Lean.Nat)
    (xs ys : ImportedScheduleChange.List_inst1 Lean.Nat) :
  Lean.eq x y -> Lean.eq xs ys ->
  Lean.eq (ImportedScheduleChange.List_cons_inst1 Lean.Nat x xs)
    (ImportedScheduleChange.List_cons_inst1 Lean.Nat y ys) :=
  fun Hx Hxs => sub_imported_eq_congr2
    (ImportedScheduleChange.List_cons_inst1 Lean.Nat) x y xs ys Hx Hxs.

Lemma sc_nat_list_source_roundtrip (xs : seq nat) :
  Logic.eq (sc_nat_list_to_source (sc_nat_list_to_imported xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn; first reflexivity.
  f_equal.
  - exact (sub_nat_rocq_roundtrip x).
  - exact IH.
Qed.

Lemma sc_nat_list_target_roundtrip
    (xs : ImportedScheduleChange.List_inst1 Lean.Nat) :
  ScNatListRel (sc_nat_list_to_source xs) xs.
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (@Lean.eq_refl _ _).
  - exact (sc_nat_list_cons_congr _ _ _ _
      (sub_nat_rel_surjective x) IH).
Qed.

Definition sc_target_zero : Lean.Nat :=
  ImportedScheduleChange.OfNat_ofNat_inst1 Lean.Nat Lean.Nat_zero
    (ImportedScheduleChange.instOfNatNat Lean.Nat_zero).

Definition sc_target_one : Lean.Nat := Lean.Nat_succ Lean.Nat_zero.

Definition sc_target_add (a b : Lean.Nat) : Lean.Nat :=
  ImportedScheduleChange.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedScheduleChange.instHAdd_inst1 Lean.Nat
      ImportedScheduleChange.instAddNat) a b.

Definition sc_target_sub (a b : Lean.Nat) : Lean.Nat :=
  ImportedScheduleChange.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedScheduleChange.instHSub_inst1 Lean.Nat
      ImportedScheduleChange.instSubNat) a b.

Lemma sc_target_add_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR + bR) (sc_target_add aL bL).
Proof. exact (sub_add_correspondence aR aL bR bL). Qed.

Lemma sc_target_succ_related nR nL :
  SubNatRel nR nL ->
  SubNatRel nR.+1 (sc_target_add nL sc_target_one).
Proof.
  intro Hn. rewrite -addn1.
  exact (sc_target_add_related nR nL 1 sc_target_one
    Hn (sub_nat_rel_canonical 1)).
Qed.

Lemma sc_target_pred_related (nR : nat) (nL : Lean.Nat) :
  SubNatRel nR nL ->
  SubNatRel nR.-1 (ImportedScheduleChange.Nat_pred nL).
Proof.
  intro Hn. unfold SubNatRel in Hn |- *.
  have Hn' := imported_eq_to_coq_eq _ _ Hn.
  rewrite <- Hn'. destruct nR; cbn; exact (@Lean.eq_refl _ _).
Qed.

Lemma sc_target_sub_succ (a b : Lean.Nat) :
  Logic.eq (sc_target_sub a (Lean.Nat_succ b))
    (ImportedScheduleChange.Nat_pred (sc_target_sub a b)).
Proof. reflexivity. Qed.

Lemma sc_target_zero_sub (b : nat) :
  Logic.eq (sc_target_sub Lean.Nat_zero (sub_nat_to_imported b))
    Lean.Nat_zero.
Proof.
  induction b as [|b IH].
  - reflexivity.
  - rewrite sc_target_sub_succ IH. reflexivity.
Qed.

Lemma sc_target_succ_sub_succ (a b : nat) :
  Logic.eq
    (sc_target_sub (Lean.Nat_succ (sub_nat_to_imported a))
      (Lean.Nat_succ (sub_nat_to_imported b)))
    (sc_target_sub (sub_nat_to_imported a) (sub_nat_to_imported b)).
Proof.
  induction b as [|b IH].
  - reflexivity.
  - rewrite !sc_target_sub_succ.
    exact (f_equal ImportedScheduleChange.Nat_pred IH).
Qed.

Lemma sc_target_sub_canonical (a b : nat) :
  Logic.eq
    (sc_target_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (a - b)).
Proof.
  induction b as [|b IH] in a |- *.
  - destruct a; reflexivity.
  - destruct a as [|a].
    + exact (sc_target_zero_sub b.+1).
    + rewrite sc_target_succ_sub_succ. exact (IH a).
Qed.

Lemma sc_target_sub_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR - bR) (sc_target_sub aL bL).
Proof.
  intros Ha Hb. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (coq_eq_to_imported_eq _ _
      (sc_target_sub_canonical aR bR)))
    (sub_imported_eq_congr2 sc_target_sub _ _ _ _ Ha Hb)).
Qed.

Definition sc_target_range (start len : Lean.Nat) :
    ImportedScheduleChange.List_inst1 Lean.Nat :=
  ImportedScheduleChange.List_range' start len sc_target_one.

Definition sc_target_index_iota (a b : Lean.Nat) :
    ImportedScheduleChange.List_inst1 Lean.Nat :=
  ImportedScheduleChange.Prosa_Util_List_index_iota a b.

Lemma sc_iota_canonical (m n : nat) :
  ScNatListRel (iota m n)
    (sc_target_range (sub_nat_to_imported m) (sub_nat_to_imported n)).
Proof.
  revert m. induction n as [|n IH]; intro m.
  - cbn [iota sc_nat_list_to_imported].
    exact (sub_imported_eq_sym _ _
      (ImportedScheduleChange.Prosa_Validation_ScheduleChangeInterface_production_range_prime_zero
        (sub_nat_to_imported m))).
  - cbn [iota sc_nat_list_to_imported].
    refine (sub_imported_eq_trans _ _ _
      (sc_nat_list_cons_congr _ _ _ _
        (@Lean.eq_refl Lean.Nat (sub_nat_to_imported m)) (IH m.+1)) _).
    exact (sub_imported_eq_sym _ _
      (ImportedScheduleChange.Prosa_Validation_ScheduleChangeInterface_production_range_prime_succ
        (sub_nat_to_imported m) (sub_nat_to_imported n))).
Qed.

Lemma sc_iota_related mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  ScNatListRel (iota mR nR) (sc_target_range mL nL).
Proof.
  intros Hm Hn. unfold ScNatListRel.
  exact (sub_imported_eq_trans _ _ _ (sc_iota_canonical mR nR)
    (sub_imported_eq_congr2 sc_target_range _ _ _ _ Hm Hn)).
Qed.

Lemma sc_index_iota_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  ScNatListRel (index_iota aR bR) (sc_target_index_iota aL bL).
Proof.
  intros Ha Hb. rewrite /index_iota.
  have Hsub := sc_target_sub_related bR bL aR aL Hb Ha.
  have Hiota := sc_iota_related aR aL (bR - aR)
    (sc_target_sub bL aL) Ha Hsub.
  unfold ScNatListRel in Hiota |- *.
  exact (sub_imported_eq_trans _ _ _ Hiota
    (sub_imported_eq_sym _ _
      (ImportedScheduleChange.Prosa_Validation_ScheduleChangeInterface_production_index_iota_eq
        aL bL))).
Qed.
