From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq fintype bigop.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedMinmax ImportedSubadditivity.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.

(** Artifact-local representation adapter for [util/minmax.v].  The actual
    Lean List and Bool datatypes below come from this Minmax export. *)

Inductive MmFalse : SProp := .
Inductive MmTrue : SProp := mm_true_intro.

Definition mm_false_elim (Q : SProp) (H : MmFalse) : Q :=
  match H return Q with end.

Definition mm_false_to_strict (H : MmFalse) :
    StrictlyInhabited Logic.False := match H with end.

Definition mm_coq_false_to_target (H : Logic.False) :
    ImportedMinmax.False := match H return ImportedMinmax.False with end.

Definition mm_target_false_to_strict (H : ImportedMinmax.False) :
    StrictlyInhabited Logic.False := match H with end.

Definition mm_bool_to_imported (b : bool) : ImportedMinmax.Bool :=
  match b with
  | true => ImportedMinmax.Bool_true
  | false => ImportedMinmax.Bool_false
  end.

Definition mm_bool_to_rocq (b : ImportedMinmax.Bool) : bool :=
  match b with
  | ImportedMinmax.Bool_true => true
  | ImportedMinmax.Bool_false => false
  end.

Definition MmBoolRel (bR : bool) (bL : ImportedMinmax.Bool) : SProp :=
  Lean.eq (mm_bool_to_imported bR) bL.

Lemma mm_bool_source_roundtrip b :
  Logic.eq (mm_bool_to_rocq (mm_bool_to_imported b)) b.
Proof. destruct b; reflexivity. Qed.

Lemma mm_bool_target_roundtrip b :
  Lean.eq (mm_bool_to_imported (mm_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Definition mm_false_ne_true
    (H : Lean.eq ImportedMinmax.Bool_false ImportedMinmax.Bool_true) :
    MmFalse :=
  match H in Lean.eq _ z return
    match z with
    | ImportedMinmax.Bool_false => MmTrue
    | ImportedMinmax.Bool_true => MmFalse
    end
  with
  | Lean.eq_refl => mm_true_intro
  end.

Lemma mm_bool_truth_correspondence bR bL : MmBoolRel bR bL ->
  PropSPropRel (is_true bR)
    (Lean.eq bL ImportedMinmax.Bool_true).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Htrue. destruct bR; cbn in Htrue.
    + exact (sub_imported_eq_sym _ _ Hb).
    + discriminate Htrue.
  - intro HL. apply strictly_inhabits.
    destruct bR; cbn.
    + reflexivity.
    + exact (False_rect _ (interpret_strict Logic.False
        (mm_false_to_strict (mm_false_ne_true
          (sub_imported_eq_trans _ _ _ Hb HL))))).
Qed.

Lemma mm_bool_false_correspondence bR bL : MmBoolRel bR bL ->
  PropSPropRel (is_true (~~ bR))
    (Lean.eq bL ImportedMinmax.Bool_false).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Hfalse. destruct bR; cbn in Hfalse.
    + discriminate Hfalse.
    + exact (sub_imported_eq_sym _ _ Hb).
  - intro HL. apply strictly_inhabits.
    destruct bR; cbn.
    + exact (False_rect _ (interpret_strict Logic.False
        (mm_false_to_strict (mm_false_ne_true
          (sub_imported_eq_sym _ _
            (sub_imported_eq_trans _ _ _ Hb HL)))))).
    + reflexivity.
Qed.

Lemma mm_bool_or_related aR aL bR bL :
  MmBoolRel aR aL -> MmBoolRel bR bL ->
  MmBoolRel (aR || bR) (ImportedMinmax.Bool_or aL bL).
Proof.
  intros Ha Hb. unfold MmBoolRel in *.
  destruct aR, bR; cbn in *;
    exact (sub_imported_eq_congr2 ImportedMinmax.Bool_or _ _ _ _ Ha Hb).
Qed.

Definition mm_target_bool_ite (A : Type) (b : ImportedMinmax.Bool)
    (t e : A) : A :=
  ImportedMinmax.ite A (Lean.eq b ImportedMinmax.Bool_true)
    (ImportedMinmax.instDecidableEqBool b ImportedMinmax.Bool_true) t e.

Lemma mm_target_bool_ite_canonical (A : Type) (b : bool) (t e : A) :
  Lean.eq (mm_target_bool_ite A (mm_bool_to_imported b) t e)
    (match b with true => t | false => e end).
Proof.
  destruct b.
  - exact (ImportedMinmax.if_pos
      (Lean.eq ImportedMinmax.Bool_true ImportedMinmax.Bool_true)
      (ImportedMinmax.instDecidableEqBool
        ImportedMinmax.Bool_true ImportedMinmax.Bool_true)
      (@Lean.eq_refl _ ImportedMinmax.Bool_true) A t e).
  - apply ImportedMinmax.if_neg.
    intro H. exact (mm_coq_false_to_target
      (interpret_strict Logic.False
        (mm_false_to_strict (mm_false_ne_true H)))).
Qed.

Definition mm_decidable_eq (T : eqType) : ImportedMinmax.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => ImportedMinmax.Decidable_isTrue (Lean.eq x y)
        (coq_eq_to_imported_eq x y H)
    | ReflectF H => ImportedMinmax.Decidable_isFalse (Lean.eq x y)
        (fun HL => mm_coq_false_to_target
          (H (imported_eq_to_coq_eq x y HL)))
    end.

Fixpoint mm_to_imported {T : Type} (xs : seq T) :
    ImportedMinmax.List T :=
  match xs with
  | [::] => ImportedMinmax.List_nil T
  | x :: tail => ImportedMinmax.List_cons T x (mm_to_imported tail)
  end.

Fixpoint mm_to_rocq {T : Type} (xs : ImportedMinmax.List T) : seq T :=
  match xs with
  | ImportedMinmax.List_nil => [::]
  | ImportedMinmax.List_cons x tail => x :: mm_to_rocq tail
  end.

Definition MmListRel {T : Type} (xsR : seq T)
    (xsL : ImportedMinmax.List T) : SProp :=
  Lean.eq (mm_to_imported xsR) xsL.

Lemma mm_list_source_roundtrip {T : Type} (xs : seq T) :
  Logic.eq (mm_to_rocq (mm_to_imported xs)) xs.
Proof. induction xs; cbn; first reflexivity. f_equal. exact IHxs. Qed.

Definition mm_target_mem {T : Type} (x : T)
    (xs : ImportedMinmax.List T) : SProp :=
  ImportedMinmax.Membership_mem T (ImportedMinmax.List T)
    (ImportedMinmax.List_instMembership T) xs x.

Definition mm_list_mem_transport {T : Type} (x : T)
    (xs ys : ImportedMinmax.List T) :
  Lean.eq xs ys -> ImportedMinmax.List_Mem T x xs ->
  ImportedMinmax.List_Mem T x ys :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ zs return ImportedMinmax.List_Mem T x zs with
    | Lean.eq_refl => Hmem
    end.

Definition mm_mem_head_of_coq_eq {T : Type} (x y : T)
    (xs : ImportedMinmax.List T) : Logic.eq x y ->
    ImportedMinmax.List_Mem T x (ImportedMinmax.List_cons T y xs) :=
  fun H => match H in Logic.eq _ z return
      ImportedMinmax.List_Mem T x (ImportedMinmax.List_cons T z xs)
    with
    | Logic.eq_refl => ImportedMinmax.List_Mem_head T x xs
    end.

Definition mm_eq_refl_truth (T : eqType) (x : T) :
    SubNatTruth (x == x).
Proof. rw eqxx. exact sub_nat_truth_intro. Defined.

Definition mm_mem_head_truth (a b : bool) :
    SubNatTruth a -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth a -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, _ => sub_nat_false_elim _
  end.

Definition mm_mem_tail_truth (a b : bool) :
    SubNatTruth b -> SubNatTruth (a || b) :=
  match a, b return SubNatTruth b -> SubNatTruth (a || b) with
  | true, _ => fun _ => sub_nat_truth_intro
  | false, true => fun _ => sub_nat_truth_intro
  | false, false => fun H => H
  end.

Fixpoint mm_seq_mem_forward {T : eqType} (x : T) (xs : seq T) :
    SubNatTruth (x \in xs) ->
    ImportedMinmax.List_Mem T x (mm_to_imported xs) :=
  match xs as zs return SubNatTruth (x \in zs) ->
      ImportedMinmax.List_Mem T x (mm_to_imported zs) with
  | [::] => sub_nat_false_elim _
  | y :: ys =>
      match @eqP T x y as r in reflect _ b return
        SubNatTruth (b || (x \in ys)) ->
        ImportedMinmax.List_Mem T x
          (ImportedMinmax.List_cons T y (mm_to_imported ys)) with
      | ReflectT Hxy => fun _ => mm_mem_head_of_coq_eq x y _ Hxy
      | ReflectF _ => fun H => ImportedMinmax.List_Mem_tail T x y _
          (mm_seq_mem_forward x ys H)
      end
  end.

Fixpoint mm_imported_mem_decoded {T : eqType} (x : T)
    (xs : ImportedMinmax.List T)
    (H : ImportedMinmax.List_Mem T x xs) :
    SubNatTruth (x \in mm_to_rocq xs) :=
  match H with
  | ImportedMinmax.List_Mem_head ys =>
      mm_mem_head_truth _ _ (mm_eq_refl_truth T x)
  | ImportedMinmax.List_Mem_tail y ys Htail =>
      mm_mem_tail_truth _ _ (mm_imported_mem_decoded x ys Htail)
  end.

Definition mm_mem_truth_transport {T : eqType} (x : T)
    (xs ys : seq T) : Logic.eq xs ys ->
    SubNatTruth (x \in xs) -> SubNatTruth (x \in ys) :=
  fun H Htruth =>
    match H in Logic.eq _ zs return
      SubNatTruth (x \in xs) -> SubNatTruth (x \in zs) with
    | Logic.eq_refl => fun Ht => Ht
    end Htruth.

Lemma mm_membership_correspondence (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedMinmax.List T) :
  MmListRel xsR xsL ->
  PropSPropRel (x \in xsR) (mm_target_mem x xsL).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intro Hmem. unfold mm_target_mem.
    apply (mm_list_mem_transport x _ _ Hxs).
    apply mm_seq_mem_forward. exact (sub_nat_prop_to_truth _ Hmem).
  - intro Hmem. apply sub_nat_truth_to_strict_prop.
    apply (mm_mem_truth_transport x _ _ (mm_list_source_roundtrip xsR)).
    apply mm_imported_mem_decoded. unfold mm_target_mem in Hmem.
    exact (mm_list_mem_transport x _ _
      (sub_imported_eq_sym _ _ Hxs) Hmem).
Qed.

Definition MmPredRel {T : Type} (PR : T -> bool)
    (PL : T -> ImportedMinmax.Bool) : SProp :=
  forall x, MmBoolRel (PR x) (PL x).

Definition mm_pred_to_imported {T : Type} (P : T -> bool) :
    T -> ImportedMinmax.Bool := fun x => mm_bool_to_imported (P x).

Lemma mm_pred_canonical {T : Type} (P : T -> bool) :
  MmPredRel P (mm_pred_to_imported P).
Proof. intro x. exact (@Lean.eq_refl _ _). Qed.

Lemma mm_pred_value_by_eq {T : Type} (P : T -> bool) (x : T) (b : bool) :
  Logic.eq (P x) b ->
  Lean.eq (mm_pred_to_imported P x) (mm_bool_to_imported b).
Proof. intro H. destruct H. exact (@Lean.eq_refl _ _). Qed.

Definition MmNatFunRel {T : Type} (FR : T -> nat)
    (FL : T -> Lean.Nat) : SProp :=
  forall x, SubNatRel (FR x) (FL x).

Definition mm_nat_fun_to_imported {T : Type} (F : T -> nat) :
    T -> Lean.Nat := fun x => sub_nat_to_imported (F x).

Lemma mm_nat_fun_canonical {T : Type} (F : T -> nat) :
  MmNatFunRel F (mm_nat_fun_to_imported F).
Proof. intro x. exact (sub_nat_rel_canonical (F x)). Qed.

Definition mm_nat_pred_to_imported (P : nat -> bool) :
    Lean.Nat -> ImportedMinmax.Bool :=
  fun n => mm_bool_to_imported (P (sub_nat_to_rocq n)).

Lemma mm_nat_pred_canonical (P : nat -> bool) (n : nat) :
  MmBoolRel (P n) (mm_nat_pred_to_imported P (sub_nat_to_imported n)).
Proof.
  unfold MmBoolRel, mm_nat_pred_to_imported.
  rewrite (sub_nat_rocq_roundtrip n).
  exact (@Lean.eq_refl _ _).
Qed.

Lemma mm_nat_pred_value_by_eq (P : nat -> bool) (n : nat) (b : bool) :
  Logic.eq (P n) b ->
  Lean.eq (mm_nat_pred_to_imported P (sub_nat_to_imported n))
    (mm_bool_to_imported b).
Proof.
  intro H. unfold mm_nat_pred_to_imported.
  rewrite (sub_nat_rocq_roundtrip n). rewrite H.
  exact (@Lean.eq_refl _ _).
Qed.

Definition mm_target_le (a b : Lean.Nat) : SProp :=
  ImportedMinmax.LE_le_inst1 Lean.Nat ImportedMinmax.instLENat a b.

Definition mm_target_lt (a b : Lean.Nat) : SProp :=
  ImportedMinmax.LT_lt_inst1 Lean.Nat ImportedMinmax.instLTNat a b.

Lemma mm_nat_le_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (leq aR bR)) (mm_target_le aL bL).
Proof.
  intros Ha Hb. unfold mm_target_le.
  change (PropSPropRel (is_true (leq aR bR))
    (ImportedSubadditivity.LE_le_inst1 Lean.Nat
      ImportedSubadditivity.instLENat aL bL)).
  exact (sub_nat_le_correspondence aR aL bR bL Ha Hb).
Qed.

Lemma mm_nat_lt_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (ltn aR bR)) (mm_target_lt aL bL).
Proof.
  intros Ha Hb. unfold mm_target_lt.
  change (PropSPropRel (is_true (ltn aR bR))
    (ImportedSubadditivity.LT_lt_inst1 Lean.Nat
      ImportedSubadditivity.instLTNat aL bL)).
  exact (sub_nat_lt_correspondence aR aL bR bL Ha Hb).
Qed.

Definition mm_target_max (a b : Lean.Nat) : Lean.Nat :=
  ImportedMinmax.Nat_max a b.

Lemma mm_max_canonical (a b : nat) :
  Lean.eq
    (mm_target_max (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (maxn a b)).
Proof.
  revert b. induction a as [|a IHa]; intro b; destruct b as [|b].
  - exact (ImportedMinmax.Prosa_Validation_MinmaxInterface_production_natMax_zero_left
      Lean.Nat_zero).
  - rewrite max0n.
    exact (ImportedMinmax.Prosa_Validation_MinmaxInterface_production_natMax_zero_left
      (sub_nat_to_imported b.+1)).
  - rewrite maxn0.
    exact (ImportedMinmax.Prosa_Validation_MinmaxInterface_production_natMax_zero_right
      (sub_nat_to_imported a.+1)).
  - rewrite maxnSS. cbn [sub_nat_to_imported].
    exact (sub_imported_eq_trans _ _ _
      (ImportedMinmax.Prosa_Validation_MinmaxInterface_production_natMax_succ_succ
        (sub_nat_to_imported a) (sub_nat_to_imported b))
      (sub_imported_eq_congr Lean.Nat_succ _ _ (IHa b))).
Qed.

Lemma mm_max_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (maxn aR bR) (mm_target_max aL bL).
Proof.
  intros Ha Hb. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (mm_max_canonical aR bR))
    (sub_imported_eq_congr2 mm_target_max _ _ _ _ Ha Hb)).
Qed.

Definition mm_target_bigMaxListCond {T : Type}
    (xs : ImportedMinmax.List T) (P : T -> ImportedMinmax.Bool)
    (F : T -> Lean.Nat) : Lean.Nat :=
  ImportedMinmax.Prosa_Util_Minmax_bigMaxListCond T xs P F.

Lemma mm_bigmax_list_cons_step (T : Type) (x : T) (xs : seq T)
    (P : T -> bool) (F : T -> nat) (b : bool) :
  Logic.eq (P x) b ->
  SubNatRel (\max_(i <- xs | P i) F i)
    (mm_target_bigMaxListCond (mm_to_imported xs)
      (mm_pred_to_imported P) (mm_nat_fun_to_imported F)) ->
  SubNatRel (\max_(i <- x :: xs | P i) F i)
    (mm_target_bigMaxListCond (mm_to_imported (x :: xs))
      (mm_pred_to_imported P) (mm_nat_fun_to_imported F)).
Proof.
  intros HP IH. rewrite big_cons HP. destruct b.
  - unfold SubNatRel, mm_target_bigMaxListCond in IH |- *.
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _
        (mm_max_canonical (F x) (\max_(i <- xs | P i) F i)))
      (sub_imported_eq_trans _ _ _
        (sub_imported_eq_congr
          (mm_target_max (sub_nat_to_imported (F x))) _ _ IH)
        (sub_imported_eq_trans _ _ _
          (sub_imported_eq_sym _ _
            (mm_target_bool_ite_canonical Lean.Nat true
              (mm_target_max (sub_nat_to_imported (F x))
                (mm_target_bigMaxListCond (mm_to_imported xs)
                  (mm_pred_to_imported P) (mm_nat_fun_to_imported F)))
              (mm_target_bigMaxListCond (mm_to_imported xs)
                (mm_pred_to_imported P) (mm_nat_fun_to_imported F))))
          (sub_imported_eq_trans _ _ _
            (sub_imported_eq_sym _ _
              (sub_imported_eq_congr
                (fun z => mm_target_bool_ite Lean.Nat z
                  (mm_target_max (sub_nat_to_imported (F x))
                    (mm_target_bigMaxListCond (mm_to_imported xs)
                      (mm_pred_to_imported P) (mm_nat_fun_to_imported F)))
                  (mm_target_bigMaxListCond (mm_to_imported xs)
                    (mm_pred_to_imported P) (mm_nat_fun_to_imported F)))
                _ _ (mm_pred_value_by_eq P x true HP)))
            (sub_imported_eq_sym _ _
              (ImportedMinmax.Prosa_Validation_MinmaxInterface_production_bigMaxListCond_cons
                T x (mm_to_imported xs) (mm_pred_to_imported P)
                (mm_nat_fun_to_imported F))))))).
  - unfold SubNatRel, mm_target_bigMaxListCond in IH |- *.
    exact (sub_imported_eq_trans _ _ _ IH
      (sub_imported_eq_trans _ _ _
        (sub_imported_eq_sym _ _
          (mm_target_bool_ite_canonical Lean.Nat false
            (mm_target_max (sub_nat_to_imported (F x))
              (mm_target_bigMaxListCond (mm_to_imported xs)
                (mm_pred_to_imported P) (mm_nat_fun_to_imported F)))
            (mm_target_bigMaxListCond (mm_to_imported xs)
              (mm_pred_to_imported P) (mm_nat_fun_to_imported F))))
        (sub_imported_eq_trans _ _ _
          (sub_imported_eq_sym _ _
            (sub_imported_eq_congr
              (fun z => mm_target_bool_ite Lean.Nat z
                (mm_target_max (sub_nat_to_imported (F x))
                  (mm_target_bigMaxListCond (mm_to_imported xs)
                    (mm_pred_to_imported P) (mm_nat_fun_to_imported F)))
                (mm_target_bigMaxListCond (mm_to_imported xs)
                  (mm_pred_to_imported P) (mm_nat_fun_to_imported F)))
              _ _ (mm_pred_value_by_eq P x false HP)))
          (sub_imported_eq_sym _ _
            (ImportedMinmax.Prosa_Validation_MinmaxInterface_production_bigMaxListCond_cons
              T x (mm_to_imported xs) (mm_pred_to_imported P)
              (mm_nat_fun_to_imported F)))))).
Qed.

Lemma mm_bigmax_list_canonical (T : Type) (xs : seq T)
    (P : T -> bool) (F : T -> nat) :
  SubNatRel (\max_(x <- xs | P x) F x)
    (mm_target_bigMaxListCond (mm_to_imported xs)
      (mm_pred_to_imported P) (mm_nat_fun_to_imported F)).
Proof.
  induction xs as [|x xs IH].
  - rewrite big_nil. unfold SubNatRel, mm_target_bigMaxListCond.
    exact (sub_imported_eq_sym _ _
      (ImportedMinmax.Prosa_Validation_MinmaxInterface_production_bigMaxListCond_nil
        T (mm_pred_to_imported P) (mm_nat_fun_to_imported F))).
  - exact (mm_bigmax_list_cons_step T x xs P F (P x)
      (Logic.eq_refl (P x)) IH).
Qed.

Definition mm_target_any {T : Type} (xs : ImportedMinmax.List T)
    (P : T -> ImportedMinmax.Bool) : ImportedMinmax.Bool :=
  ImportedMinmax.List_any T xs P.

Lemma mm_any_canonical (T : Type) (xs : seq T) (P : T -> bool) :
  MmBoolRel (has P xs)
    (mm_target_any (mm_to_imported xs) (mm_pred_to_imported P)).
Proof.
  induction xs as [|x xs IH].
  - exact (sub_imported_eq_sym _ _
      (ImportedMinmax.Prosa_Validation_MinmaxInterface_production_any_nil
        T (mm_pred_to_imported P))).
  - exact (sub_imported_eq_trans _ _ _
      (mm_bool_or_related _ _ _ _ (@Lean.eq_refl _ _) IH)
      (sub_imported_eq_sym _ _
        (ImportedMinmax.Prosa_Validation_MinmaxInterface_production_any_cons
          T x (mm_to_imported xs) (mm_pred_to_imported P)))).
Qed.

Definition MmOrdRel (n : nat) (iR : 'I_n)
    (iL : Fin (sub_nat_to_imported n)) : SProp :=
  SubNatRel (nat_of_ord iR)
    (ImportedMinmax.Fin_val (sub_nat_to_imported n) iL).

Definition mm_ord_to_fin (n : nat) (i : 'I_n) :
    Fin (sub_nat_to_imported n).
Proof.
  refine (Fin_mk (sub_nat_to_imported n)
    (sub_nat_to_imported (nat_of_ord i)) _).
  exact (prop_to_sprop _ _
    (mm_nat_lt_correspondence (nat_of_ord i)
      (sub_nat_to_imported (nat_of_ord i)) n (sub_nat_to_imported n)
      (sub_nat_rel_canonical (nat_of_ord i)) (sub_nat_rel_canonical n))
    (ltn_ord i)).
Defined.

Definition mm_target_bigMaxNatRange (n : Lean.Nat)
    (P : Lean.Nat -> ImportedMinmax.Bool) : Lean.Nat :=
  ImportedMinmax.Prosa_Util_Minmax_bigMaxNatRange n P.

Lemma mm_source_bigmax_range_succ (n : nat) (P : nat -> bool) :
  Logic.eq (\max_(i < n.+1 | P i) i)
    (maxn (\max_(i < n | P i) i) (if P n then n else O)).
Proof. by rewrite !big_mkcond big_ord_recr /= -big_mkcond. Qed.

Lemma mm_bigmax_range_succ_step (n : nat) (P : nat -> bool) (b : bool) :
  Logic.eq (P n) b ->
  SubNatRel (\max_(i < n | P i) i)
    (mm_target_bigMaxNatRange (sub_nat_to_imported n)
      (mm_nat_pred_to_imported P)) ->
  SubNatRel (\max_(i < n.+1 | P i) i)
    (mm_target_bigMaxNatRange (sub_nat_to_imported n.+1)
      (mm_nat_pred_to_imported P)).
Proof.
  intros HP IH. rewrite mm_source_bigmax_range_succ HP. destruct b.
  - unfold SubNatRel, mm_target_bigMaxNatRange in IH |- *.
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _
        (mm_max_canonical (\max_(i < n | P i) i) n))
      (sub_imported_eq_trans _ _ _
        (sub_imported_eq_congr
          (fun z => mm_target_max z (sub_nat_to_imported n)) _ _ IH)
        (sub_imported_eq_trans _ _ _
          (sub_imported_eq_sym _ _
            (mm_target_bool_ite_canonical Lean.Nat true
              (mm_target_max
                (mm_target_bigMaxNatRange (sub_nat_to_imported n)
                  (mm_nat_pred_to_imported P))
                (sub_nat_to_imported n))
              (mm_target_bigMaxNatRange (sub_nat_to_imported n)
                (mm_nat_pred_to_imported P))))
          (sub_imported_eq_trans _ _ _
            (sub_imported_eq_sym _ _
              (sub_imported_eq_congr
                (fun z => mm_target_bool_ite Lean.Nat z
                  (mm_target_max
                    (mm_target_bigMaxNatRange (sub_nat_to_imported n)
                      (mm_nat_pred_to_imported P))
                    (sub_nat_to_imported n))
                  (mm_target_bigMaxNatRange (sub_nat_to_imported n)
                    (mm_nat_pred_to_imported P)))
                _ _ (mm_nat_pred_value_by_eq P n true HP)))
            (sub_imported_eq_sym _ _
              (ImportedMinmax.Prosa_Validation_MinmaxInterface_production_bigMaxNatRange_succ
                (sub_nat_to_imported n) (mm_nat_pred_to_imported P))))))).
  - rewrite maxn0.
    unfold SubNatRel, mm_target_bigMaxNatRange in IH |- *.
    exact (sub_imported_eq_trans _ _ _ IH
      (sub_imported_eq_trans _ _ _
        (sub_imported_eq_sym _ _
          (mm_target_bool_ite_canonical Lean.Nat false
            (mm_target_max
              (mm_target_bigMaxNatRange (sub_nat_to_imported n)
                (mm_nat_pred_to_imported P))
              (sub_nat_to_imported n))
            (mm_target_bigMaxNatRange (sub_nat_to_imported n)
              (mm_nat_pred_to_imported P))))
        (sub_imported_eq_trans _ _ _
          (sub_imported_eq_sym _ _
            (sub_imported_eq_congr
              (fun z => mm_target_bool_ite Lean.Nat z
                (mm_target_max
                  (mm_target_bigMaxNatRange (sub_nat_to_imported n)
                    (mm_nat_pred_to_imported P))
                  (sub_nat_to_imported n))
                (mm_target_bigMaxNatRange (sub_nat_to_imported n)
                  (mm_nat_pred_to_imported P)))
              _ _ (mm_nat_pred_value_by_eq P n false HP)))
          (sub_imported_eq_sym _ _
            (ImportedMinmax.Prosa_Validation_MinmaxInterface_production_bigMaxNatRange_succ
              (sub_nat_to_imported n) (mm_nat_pred_to_imported P)))))).
Qed.

Lemma mm_bigmax_range_canonical (n : nat) (P : nat -> bool) :
  SubNatRel (\max_(i < n | P i) i)
    (mm_target_bigMaxNatRange (sub_nat_to_imported n)
      (mm_nat_pred_to_imported P)).
Proof.
  induction n as [|n IH].
  - rewrite big_ord0. unfold SubNatRel, mm_target_bigMaxNatRange.
    exact (sub_imported_eq_sym _ _
      (ImportedMinmax.Prosa_Validation_MinmaxInterface_production_bigMaxNatRange_zero
        (mm_nat_pred_to_imported P))).
  - exact (mm_bigmax_range_succ_step n P (P n)
      (Logic.eq_refl (P n)) IH).
Qed.

Lemma mm_bigmax_range_true_canonical (n : nat) :
  SubNatRel (\max_(i < n) i)
    (mm_target_bigMaxNatRange (sub_nat_to_imported n)
      (fun _ => ImportedMinmax.Bool_true)).
Proof.
  have H := mm_bigmax_range_canonical n (fun _ => true).
  exact H.
Qed.

Lemma mm_nat_value_eq_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof. exact (sub_nat_eq_correspondence aR aL bR bL). Qed.
