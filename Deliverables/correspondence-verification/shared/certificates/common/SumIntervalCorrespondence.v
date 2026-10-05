From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq bigop.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSumInterval ImportedSubadditivity.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.

(** Computational correspondence for the exact normalized finite-sum
    interface exported from the fresh compiled [Prosa.Util.Sum] artifact. *)

Definition sum_target_one : Lean.Nat :=
  ImportedSumInterval.OfNat_ofNat_inst1 Lean.Nat (Lean.Nat_succ Lean.Nat_zero)
    (ImportedSumInterval.instOfNatNat (Lean.Nat_succ Lean.Nat_zero)).

Definition sum_target_function (F : nat -> nat) : Lean.Nat -> Lean.Nat :=
  fun n => sub_nat_to_imported (F (sub_nat_to_rocq n)).

Lemma sum_target_add_canonical (a b : nat) :
  Lean.eq
    (Lean.Nat_add
      (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (a + b)).
Proof. exact (sub_add_canonical a b). Qed.

Lemma sum_target_add_canonical_prop (a b : nat) :
  Logic.eq
    (Lean.Nat_add
      (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (a + b)).
Proof. exact (imported_eq_to_coq_eq _ _ (sum_target_add_canonical a b)). Qed.

Lemma sum_target_sub_succ_prop (a b : Lean.Nat) :
  Logic.eq
    (ImportedSumInterval.Nat_sub a (Lean.Nat_succ b))
    (ImportedSumInterval.Nat_pred (ImportedSumInterval.Nat_sub a b)).
Proof. reflexivity. Qed.

Lemma sum_target_zero_sub_prop (b : nat) :
  Logic.eq
    (ImportedSumInterval.Nat_sub Lean.Nat_zero (sub_nat_to_imported b))
    Lean.Nat_zero.
Proof.
  induction b as [|b IH].
  - reflexivity.
  - rw sum_target_sub_succ_prop IH. reflexivity.
Qed.

Lemma sum_target_succ_sub_succ_prop (a b : nat) :
  Logic.eq
    (ImportedSumInterval.Nat_sub
      (Lean.Nat_succ (sub_nat_to_imported a))
      (Lean.Nat_succ (sub_nat_to_imported b)))
    (ImportedSumInterval.Nat_sub
      (sub_nat_to_imported a) (sub_nat_to_imported b)).
Proof.
  induction b as [|b IH].
  - reflexivity.
  - rw !sum_target_sub_succ_prop.
    exact (f_equal ImportedSumInterval.Nat_pred IH).
Qed.

Lemma sum_target_sub_canonical_prop (a b : nat) :
  Logic.eq
    (ImportedSumInterval.Nat_sub
      (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (a - b)).
Proof.
  induction b as [|b IH] in a |- *.
  - destruct a; reflexivity.
  - destruct a as [|a].
    + exact (sum_target_zero_sub_prop b.+1).
    + rw sum_target_succ_sub_succ_prop. exact (IH a).
Qed.

Lemma sum_target_range_succ_prop (start len step : Lean.Nat) :
  Logic.eq
    (ImportedSumInterval.List_range' start (Lean.Nat_succ len) step)
    (ImportedSumInterval.List_cons_inst1 Lean.Nat start
      (ImportedSumInterval.List_range'
        (Lean.Nat_add start step) len step)).
Proof. reflexivity. Qed.

Lemma sum_target_map_cons_prop {A B : Type} (f : A -> B) (x : A)
    (xs : ImportedSumInterval.List_inst1 A) :
  Logic.eq
    (ImportedSumInterval.List_map_inst3 A B f
      (ImportedSumInterval.List_cons_inst1 A x xs))
    (ImportedSumInterval.List_cons_inst1 B (f x)
      (ImportedSumInterval.List_map_inst3 A B f xs)).
Proof. reflexivity. Qed.

Lemma sum_target_foldr_cons_prop {A B : Type} (f : A -> B -> B)
    (z : B) (x : A) (xs : ImportedSumInterval.List_inst1 A) :
  Logic.eq
    (ImportedSumInterval.List_foldr_inst3 A B f z
      (ImportedSumInterval.List_cons_inst1 A x xs))
    (f x (ImportedSumInterval.List_foldr_inst3 A B f z xs)).
Proof. reflexivity. Qed.

Fixpoint sum_seq_to_target (xs : seq nat) :
    ImportedSumInterval.List_inst1 Lean.Nat :=
  match xs with
  | [::] => ImportedSumInterval.List_nil_inst1 Lean.Nat
  | x :: xs' => ImportedSumInterval.List_cons_inst1 Lean.Nat
      (sub_nat_to_imported x) (sum_seq_to_target xs')
  end.

Lemma sum_target_range_iota_prop (start len : nat) :
  Logic.eq
    (ImportedSumInterval.List_range'
      (sub_nat_to_imported start) (sub_nat_to_imported len) sum_target_one)
    (sum_seq_to_target (iota start len)).
Proof.
  elim: len start => [|len IH] start.
  - reflexivity.
  - cbn [sub_nat_to_imported iota sum_seq_to_target].
    rw sum_target_range_succ_prop.
    have Hstart : Logic.eq
        (Lean.Nat_add
          (sub_nat_to_imported start) sum_target_one)
        (sub_nat_to_imported start.+1) by reflexivity.
    rw Hstart (IH start.+1). reflexivity.
Qed.

Lemma sum_target_map_converted_prop (F : nat -> nat) (xs : seq nat) :
  Logic.eq
    (ImportedSumInterval.List_map_inst3 Lean.Nat Lean.Nat
      (sum_target_function F) (sum_seq_to_target xs))
    (sum_seq_to_target (map F xs)).
Proof.
  elim: xs => [|x xs IH].
  - reflexivity.
  - cbn [sum_seq_to_target]. rw sum_target_map_cons_prop.
    unfold sum_target_function.
    rw sub_nat_rocq_roundtrip IH. reflexivity.
Qed.

Definition sum_target_list_sum
    (xs : ImportedSumInterval.List_inst1 Lean.Nat) : Lean.Nat :=
  ImportedSumInterval.List_foldr_inst3 Lean.Nat Lean.Nat
    Lean.Nat_add Lean.Nat_zero xs.

Lemma sum_target_list_sum_converted_prop (xs : seq nat) :
  Logic.eq (sum_target_list_sum (sum_seq_to_target xs))
    (sub_nat_to_imported (foldr addn O xs)).
Proof.
  elim: xs => [|x xs IH].
  - reflexivity.
  - cbn [sum_seq_to_target foldr].
    unfold sum_target_list_sum.
    unfold sum_target_list_sum in IH.
    rw sum_target_foldr_cons_prop IH.
    exact (sum_target_add_canonical_prop x (foldr addn O xs)).
Qed.

Definition sum_target_interval_value
    (m n : nat) (F : nat -> nat) : Lean.Nat :=
  sum_target_list_sum
    (ImportedSumInterval.List_map_inst3 Lean.Nat Lean.Nat
      (sum_target_function F)
      (ImportedSumInterval.List_range'
        (sub_nat_to_imported m)
        (ImportedSumInterval.Nat_sub
          (sub_nat_to_imported n) (sub_nat_to_imported m))
        sum_target_one)).

Lemma mathcomp_big_seq_as_fold (xs : seq nat) (F : nat -> nat) :
  Logic.eq (\sum_(i <- xs) F i) (foldr addn O (map F xs)).
Proof.
  elim: xs => [|x xs IH].
  - rw big_nil. reflexivity.
  - rw big_cons. cbn [map foldr]. now rw IH.
Qed.

Lemma sum_target_interval_value_prop (m n : nat) (F : nat -> nat) :
  Logic.eq (sum_target_interval_value m n F)
    (sub_nat_to_imported (\sum_(m <= i < n) F i)).
Proof.
  unfold sum_target_interval_value.
  rw sum_target_sub_canonical_prop.
  rw sum_target_range_iota_prop.
  rw sum_target_map_converted_prop.
  rw sum_target_list_sum_converted_prop.
  rw /index_iota mathcomp_big_seq_as_fold.
  reflexivity.
Qed.

Theorem finite_nat_sum_value_correspondence (m n : nat) (F : nat -> nat) :
  Lean.eq (sum_target_interval_value m n F)
    (sub_nat_to_imported (\sum_(m <= i < n) F i)).
Proof.
  exact (coq_eq_to_imported_eq _ _
    (sum_target_interval_value_prop m n F)).
Qed.

(** A relation-first interface for arbitrary related endpoints and functions.
    The earlier [sum_target_interval_value] is the canonical specialization;
    these definitions let theorem-level certificates quantify over the actual
    imported Lean binders without assuming that they were constructed by the
    source-to-target map. *)

Definition si_target_add (a b : Lean.Nat) : Lean.Nat :=
  ImportedSumInterval.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedSumInterval.instHAdd_inst1 Lean.Nat
      ImportedSumInterval.instAddNat) a b.

Definition si_target_sub (a b : Lean.Nat) : Lean.Nat :=
  ImportedSumInterval.Nat_sub a b.

Definition si_target_interval_value
    (m n : Lean.Nat) (F : Lean.Nat -> Lean.Nat) : Lean.Nat :=
  sum_target_list_sum
    (ImportedSumInterval.List_map_inst3 Lean.Nat Lean.Nat F
      (ImportedSumInterval.List_range' m (si_target_sub n m)
        sum_target_one)).

Definition SiNatFunRel (FR : nat -> nat)
    (FL : Lean.Nat -> Lean.Nat) : SProp :=
  SubNatFunRel FR FL.

Definition si_nat_fun_to_imported (F : nat -> nat) :
    Lean.Nat -> Lean.Nat :=
  fun n => sub_nat_to_imported (F (sub_nat_to_rocq n)).

Definition si_nat_fun_to_rocq (F : Lean.Nat -> Lean.Nat) :
    nat -> nat :=
  fun n => sub_nat_to_rocq (F (sub_nat_to_imported n)).

Lemma si_nat_fun_canonical (F : nat -> nat) :
  SiNatFunRel F (si_nat_fun_to_imported F).
Proof.
  intros nR nL Hn. unfold SubNatRel in Hn |- *.
  destruct Hn. unfold si_nat_fun_to_imported.
  rewrite sub_nat_rocq_roundtrip.
  exact (@Lean.eq_refl _ _).
Qed.

Lemma si_nat_fun_surjective (F : Lean.Nat -> Lean.Nat) :
  SiNatFunRel (si_nat_fun_to_rocq F) F.
Proof.
  intros nR nL Hn. unfold SubNatRel in Hn |- *.
  destruct Hn. unfold si_nat_fun_to_rocq.
  exact (sub_nat_imported_roundtrip (F (sub_nat_to_imported nR))).
Qed.

Definition SiNatListRel (xsR : seq nat)
    (xsL : ImportedSumInterval.List_inst1 Lean.Nat) : SProp :=
  Lean.eq (sum_seq_to_target xsR) xsL.

Lemma si_range_related (start len : nat) :
  SiNatListRel (iota start len)
    (ImportedSumInterval.List_range'
      (sub_nat_to_imported start) (sub_nat_to_imported len)
      sum_target_one).
Proof.
  unfold SiNatListRel.
  exact (coq_eq_to_imported_eq _ _
    (Logic.eq_sym (sum_target_range_iota_prop start len))).
Qed.

Fixpoint si_map_related_canonical
    (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat)
    (HF : SiNatFunRel FR FL) (xs : seq nat) :
  Lean.eq (sum_seq_to_target (map FR xs))
    (ImportedSumInterval.List_map_inst3 Lean.Nat Lean.Nat FL
      (sum_seq_to_target xs)) :=
  match xs with
  | [::] => @Lean.eq_refl _ _
  | x :: xs' => sub_imported_eq_congr2
      (ImportedSumInterval.List_cons_inst1 Lean.Nat) _ _ _ _
      (HF x (sub_nat_to_imported x) (sub_nat_rel_canonical x))
      (si_map_related_canonical FR FL HF xs')
  end.

Lemma si_map_related (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat)
    (xsR : seq nat) (xsL : ImportedSumInterval.List_inst1 Lean.Nat) :
  SiNatFunRel FR FL -> SiNatListRel xsR xsL ->
  SiNatListRel (map FR xsR)
    (ImportedSumInterval.List_map_inst3 Lean.Nat Lean.Nat FL xsL).
Proof.
  intros HF Hxs. unfold SiNatListRel in *.
  destruct Hxs. exact (si_map_related_canonical FR FL HF xsR).
Qed.

Lemma si_list_sum_related (xsR : seq nat)
    (xsL : ImportedSumInterval.List_inst1 Lean.Nat) :
  SiNatListRel xsR xsL ->
  SubNatRel (foldr addn O xsR) (sum_target_list_sum xsL).
Proof.
  intro Hxs. unfold SiNatListRel in Hxs. destruct Hxs.
  unfold SubNatRel.
  exact (sub_imported_eq_sym _ _
    (coq_eq_to_imported_eq _ _
      (sum_target_list_sum_converted_prop xsR))).
Qed.

Lemma si_target_sub_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR - bR) (si_target_sub aL bL).
Proof.
  intros Ha Hb. unfold SubNatRel, si_target_sub in *.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _
      (coq_eq_to_imported_eq _ _ (sum_target_sub_canonical_prop aR bR)))
    (sub_imported_eq_congr2 ImportedSumInterval.Nat_sub _ _ _ _ Ha Hb)).
Qed.

Lemma si_target_add_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR + bR) (si_target_add aL bL).
Proof. exact (sub_add_correspondence aR aL bR bL). Qed.

Lemma si_interval_sum_related
    (mR nR : nat) (mL nL : Lean.Nat)
    (FR : nat -> nat) (FL : Lean.Nat -> Lean.Nat) :
  SubNatRel mR mL -> SubNatRel nR nL -> SiNatFunRel FR FL ->
  SubNatRel (\sum_(mR <= i < nR) FR i)
    (si_target_interval_value mL nL FL).
Proof.
  intros Hm Hn HF.
  unfold si_target_interval_value.
  rewrite /index_iota mathcomp_big_seq_as_fold.
  apply si_list_sum_related.
  apply si_map_related.
  - exact HF.
  - unfold SiNatListRel. unfold SubNatRel in Hm, Hn.
    exact (sub_imported_eq_trans _ _ _
      (si_range_related mR (nR - mR))
      (sub_imported_eq_congr2
        (fun start len => ImportedSumInterval.List_range'
          start len sum_target_one) _ _ _ _ Hm
        (si_target_sub_related nR nL mR mL Hn Hm))).
Qed.

(** Namespace-local Bool realization for the same approved Bool relation.
    This adapter is needed because each lean4export artifact is sealed in its
    own Rocq module. *)
Definition si_bool_to_imported (b : bool) : ImportedSumInterval.Bool :=
  match b with
  | true => ImportedSumInterval.Bool_true
  | false => ImportedSumInterval.Bool_false
  end.

Definition si_bool_to_rocq (b : ImportedSumInterval.Bool) : bool :=
  match b with
  | ImportedSumInterval.Bool_true => true
  | ImportedSumInterval.Bool_false => false
  end.

Definition SiBoolRel (bR : bool) (bL : ImportedSumInterval.Bool) : SProp :=
  Lean.eq (si_bool_to_imported bR) bL.

Lemma si_bool_source_roundtrip b :
  Logic.eq (si_bool_to_rocq (si_bool_to_imported b)) b.
Proof. destruct b; reflexivity. Qed.

Lemma si_bool_target_roundtrip b :
  Lean.eq (si_bool_to_imported (si_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Lemma si_bool_and_related aR aL bR bL :
  SiBoolRel aR aL -> SiBoolRel bR bL ->
  SiBoolRel (aR && bR) (ImportedSumInterval.Bool_and aL bL).
Proof.
  intros Ha Hb. unfold SiBoolRel in *.
  destruct aR, bR; cbn in *;
    exact (sub_imported_eq_congr2 ImportedSumInterval.Bool_and _ _ _ _ Ha Hb).
Qed.

Definition SiBoolPredRel (PR : nat -> bool)
    (PL : Lean.Nat -> ImportedSumInterval.Bool) : SProp :=
  forall nR nL, SubNatRel nR nL -> SiBoolRel (PR nR) (PL nL).

Definition si_bool_pred_to_imported (P : nat -> bool) :
    Lean.Nat -> ImportedSumInterval.Bool :=
  fun n => si_bool_to_imported (P (sub_nat_to_rocq n)).

Definition si_bool_pred_to_rocq
    (P : Lean.Nat -> ImportedSumInterval.Bool) : nat -> bool :=
  fun n => si_bool_to_rocq (P (sub_nat_to_imported n)).

Lemma si_bool_pred_canonical P :
  SiBoolPredRel P (si_bool_pred_to_imported P).
Proof.
  intros nR nL Hn. unfold SubNatRel in Hn. destruct Hn.
  unfold SiBoolRel, si_bool_pred_to_imported.
  rewrite sub_nat_rocq_roundtrip. exact (@Lean.eq_refl _ _).
Qed.

Lemma si_bool_pred_surjective P :
  SiBoolPredRel (si_bool_pred_to_rocq P) P.
Proof.
  intros nR nL Hn. unfold SubNatRel in Hn. destruct Hn.
  unfold SiBoolRel, si_bool_pred_to_rocq.
  exact (si_bool_target_roundtrip (P (sub_nat_to_imported nR))).
Qed.

Definition si_source_bool_nat (b : bool) : nat :=
  if b then 1%N else 0%N.

Definition si_target_bool_nat (b : ImportedSumInterval.Bool) : Lean.Nat :=
  ImportedSumInterval.Bool_toNat b.

Lemma si_bool_nat_related bR bL :
  SiBoolRel bR bL ->
  SubNatRel (si_source_bool_nat bR) (si_target_bool_nat bL).
Proof.
  intro Hb. unfold SiBoolRel in Hb. destruct bR; cbn in Hb |- *;
    destruct Hb; exact (@Lean.eq_refl _ _).
Qed.

Lemma si_bool_interval_sum_related
    (mR nR : nat) (mL nL : Lean.Nat)
    (PR : nat -> bool) (PL : Lean.Nat -> ImportedSumInterval.Bool) :
  SubNatRel mR mL -> SubNatRel nR nL -> SiBoolPredRel PR PL ->
  SubNatRel (\sum_(mR <= i < nR) si_source_bool_nat (PR i))
    (si_target_interval_value mL nL
      (fun i => si_target_bool_nat (PL i))).
Proof.
  intros Hm Hn HP. apply si_interval_sum_related; try assumption.
  intros iR iL Hi. exact (si_bool_nat_related _ _ (HP _ _ Hi)).
Qed.

Definition si_target_decide_nat_eq (a b : Lean.Nat) :
    ImportedSumInterval.Bool :=
  ImportedSumInterval.Decidable_decide (Lean.eq a b)
    (ImportedSumInterval.instDecidableEqNat a b).

Definition si_false_elim (Q : SProp) (H : ImportedSumInterval.False) : Q :=
  match H return Q with end.

Definition si_false_to_strict (H : ImportedSumInterval.False) :
  StrictlyInhabited Logic.False := match H with end.

Definition si_coq_false_to_target (H : Logic.False) :
    ImportedSumInterval.False := match H return ImportedSumInterval.False with end.

Lemma si_bool_true_correspondence bR bL :
  SiBoolRel bR bL ->
  PropSPropRel (is_true bR)
    (Lean.eq bL ImportedSumInterval.Bool_true).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Htrue. destruct bR; cbn in Htrue.
    + exact (sub_imported_eq_sym _ _ Hb).
    + discriminate Htrue.
  - intro HL. apply strictly_inhabits.
    destruct bR; cbn.
    + reflexivity.
    + exact (False_rect _ (interpret_strict Logic.False
        (si_false_to_strict
          (ImportedSumInterval.Bool_noConfusion_inst1
            ImportedSumInterval.False ImportedSumInterval.Bool_false
            ImportedSumInterval.Bool_true
            (sub_imported_eq_trans _ _ _ Hb HL))))).
Qed.

Lemma si_decide_bool_correspondence (b : bool) (Q : SProp)
    (d : ImportedSumInterval.Decidable Q) :
  PropSPropRel (is_true b) Q ->
  SiBoolRel b (ImportedSumInterval.Decidable_decide Q d).
Proof.
  intro Hrel. unfold SiBoolRel.
  destruct d as [Hfalse | Htrue]; destruct b; cbn.
  - exact (si_false_elim _
      (Hfalse (prop_to_sprop _ _ Hrel (Logic.eq_refl true)))).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - exact (si_false_elim _ (si_coq_false_to_target
      (match sprop_to_prop _ _ Hrel Htrue with end))).
Qed.

Lemma si_decide_nat_eq_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SiBoolRel (aR == bR) (si_target_decide_nat_eq aL bL).
Proof.
  intros Ha Hb. apply si_decide_bool_correspondence.
  apply prop_sprop_rel_intro.
  - intro Hbool. apply (prop_to_sprop _ _
      (sub_nat_eq_correspondence aR aL bR bL Ha Hb)).
    by move/eqP: Hbool.
  - intro Heq. apply strictly_inhabits. apply/eqP.
    exact (sprop_to_prop _ _
      (sub_nat_eq_correspondence aR aL bR bL Ha Hb) Heq).
Qed.
