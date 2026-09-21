From mathcomp Require Import ssreflect ssrbool ssrnat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedUnitGrowth.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  NatSubCorrespondence.
Require Import GeneratedUnitGrowthSource.

(** Adapters for the operations occurring in the freshly imported
    [Prosa.Util.UnitGrowth] artifact. *)
Definition ug_add (a b : Lean.Nat) : Lean.Nat :=
  ImportedUnitGrowth.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedUnitGrowth.instHAdd_inst1 Lean.Nat
      ImportedUnitGrowth.instAddNat) a b.

Definition ug_sub (a b : Lean.Nat) : Lean.Nat :=
  ImportedUnitGrowth.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedUnitGrowth.instHSub_inst1 Lean.Nat
      ImportedUnitGrowth.instSubNat) a b.

Definition ug_le (a b : Lean.Nat) : SProp :=
  ImportedUnitGrowth.LE_le_inst1 Lean.Nat ImportedUnitGrowth.instLENat a b.

Definition ug_lt (a b : Lean.Nat) : SProp :=
  ImportedUnitGrowth.LT_lt_inst1 Lean.Nat ImportedUnitGrowth.instLTNat a b.

Definition ug_zero : Lean.Nat :=
  ImportedUnitGrowth.OfNat_ofNat_inst1 Lean.Nat Lean.Nat_zero
    (ImportedUnitGrowth.instOfNatNat Lean.Nat_zero).

Definition ug_one : Lean.Nat :=
  ImportedUnitGrowth.OfNat_ofNat_inst1 Lean.Nat (Lean.Nat_succ Lean.Nat_zero)
    (ImportedUnitGrowth.instOfNatNat (Lean.Nat_succ Lean.Nat_zero)).

Definition ug_min (a b : Lean.Nat) : Lean.Nat :=
  ImportedUnitGrowth.Min_min_inst1 Lean.Nat ImportedUnitGrowth.instMinNat a b.

Definition ug_decide_le (a b : Lean.Nat) : ImportedUnitGrowth.Bool :=
  ImportedUnitGrowth.Decidable_decide (ug_le a b)
    (ImportedUnitGrowth.Nat_decLe a b).

Lemma ug_add_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR + bR) (ug_add aL bL).
Proof. exact (sub_add_correspondence aR aL bR bL). Qed.

Lemma ug_sub_zero (a : Lean.Nat) :
  Lean.eq (ug_sub a Lean.Nat_zero) a.
Proof. exact (@Lean.eq_refl Lean.Nat a). Qed.

Lemma ug_sub_succ (a b : Lean.Nat) :
  Lean.eq (ug_sub a (Lean.Nat_succ b))
    (ImportedUnitGrowth.Nat_pred (ug_sub a b)).
Proof.
  exact (@Lean.eq_refl Lean.Nat
    (ImportedUnitGrowth.Nat_pred (ug_sub a b))).
Qed.

Definition ug_pred_canonical (n : nat) :
  Lean.eq (ImportedUnitGrowth.Nat_pred (sub_nat_to_imported n))
    (sub_nat_to_imported (Nat.pred n)) :=
  match n return
    Lean.eq (ImportedUnitGrowth.Nat_pred (sub_nat_to_imported n))
      (sub_nat_to_imported (Nat.pred n))
  with
  | O => @Lean.eq_refl Lean.Nat Lean.Nat_zero
  | S n' => @Lean.eq_refl Lean.Nat (sub_nat_to_imported n')
  end.

Lemma ug_sub_iterated_pred (a b : nat) :
  Lean.eq
    (ug_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (rocq_iterated_pred a b)).
Proof.
  induction b as [|b IH].
  - exact (ug_sub_zero (sub_nat_to_imported a)).
  - exact (sub_imported_eq_trans _ _ _
      (ug_sub_succ _ _)
      (sub_imported_eq_trans _ _ _
        (sub_imported_eq_congr ImportedUnitGrowth.Nat_pred _ _ IH)
        (ug_pred_canonical (rocq_iterated_pred a b)))).
Qed.

Lemma ug_sub_canonical (a b : nat) :
  Lean.eq
    (ug_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (a - b)).
Proof.
  exact (sub_imported_eq_trans _ _ _
    (ug_sub_iterated_pred a b)
    (coq_eq_to_imported_eq _ _
      (f_equal sub_nat_to_imported (rocq_iterated_pred_is_subn a b)))).
Qed.

Lemma ug_sub_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR - bR) (ug_sub aL bL).
Proof.
  intros Ha Hb. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (ug_sub_canonical aR bR))
    (sub_imported_eq_congr2 ug_sub _ _ _ _ Ha Hb)).
Qed.

Lemma ug_le_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (leq aR bR)) (ug_le aL bL).
Proof. exact (sub_nat_le_correspondence aR aL bR bL). Qed.

Lemma ug_lt_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (ltn aR bR)) (ug_lt aL bL).
Proof. exact (sub_nat_lt_correspondence aR aL bR bL). Qed.

Lemma ug_eq_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof. exact (sub_nat_eq_correspondence aR aL bR bL). Qed.

Definition ug_zero_rel : SubNatRel O ug_zero :=
  @Lean.eq_refl Lean.Nat Lean.Nat_zero.

Definition ug_one_rel : SubNatRel 1 ug_one :=
  @Lean.eq_refl Lean.Nat (Lean.Nat_succ Lean.Nat_zero).

Definition ug_imported_false_elim (P : SProp)
    (H : ImportedUnitGrowth.False) : P := match H return P with end.

Definition ug_coq_false_to_imported_false
    (H : Logic.False) : ImportedUnitGrowth.False :=
  match H return ImportedUnitGrowth.False with end.

Definition ug_bool_false_elim (H : is_true false) : Logic.False.
Proof. discriminate H. Defined.

Lemma ug_min_left (a b : Lean.Nat) :
  ug_le a b -> Lean.eq (ug_min a b) a.
Proof.
  intro Hle. unfold ug_min, ImportedUnitGrowth.Min_min_inst1,
    ImportedUnitGrowth.instMinNat, ImportedUnitGrowth.minOfLe_inst1.
  cbn. destruct (ImportedUnitGrowth.Nat_decLe a b) as [Hno|Hyes].
  - exact (ug_imported_false_elim _ (Hno Hle)).
  - exact (@Lean.eq_refl Lean.Nat a).
Qed.

Lemma ug_min_right (a b : Lean.Nat) :
  (ug_le a b -> ImportedUnitGrowth.False) ->
  Lean.eq (ug_min a b) b.
Proof.
  intro Hnot. unfold ug_min, ImportedUnitGrowth.Min_min_inst1,
    ImportedUnitGrowth.instMinNat, ImportedUnitGrowth.minOfLe_inst1.
  cbn. destruct (ImportedUnitGrowth.Nat_decLe a b) as [Hno|Hyes].
  - exact (@Lean.eq_refl Lean.Nat b).
  - exact (ug_imported_false_elim _ (Hnot Hyes)).
Qed.

Lemma ug_min_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (minn aR bR) (ug_min aL bL).
Proof.
  intros Ha Hb. have Hle := ug_le_correspondence _ _ _ _ Ha Hb.
  destruct (leqP aR bR) as [Hab|Hba].
  - unfold SubNatRel.
    exact (sub_imported_eq_trans _ _ _ Ha
      (sub_imported_eq_sym _ _
        (ug_min_left aL bL
          (prop_to_sprop _ _ Hle (Logic.eq_refl true))))).
  - unfold SubNatRel.
    have HnotL : ug_le aL bL -> ImportedUnitGrowth.False :=
      fun HL => ug_coq_false_to_imported_false
        (ug_bool_false_elim (sprop_to_prop _ _ Hle HL)).
    exact (sub_imported_eq_trans _ _ _ Hb
      (sub_imported_eq_sym _ _ (ug_min_right aL bL HnotL))).
Qed.

Inductive UgTruth : SProp := ug_truth_intro.
Inductive UgFalse : SProp := .

Definition UgBoolTruth (b : bool) : SProp :=
  match b with true => UgTruth | false => UgFalse end.

Definition UgBoolRel
    (bR : bool) (bL : ImportedUnitGrowth.Bool) : SProp :=
  match bR, bL with
  | true, ImportedUnitGrowth.Bool_true => UgTruth
  | false, ImportedUnitGrowth.Bool_false => UgTruth
  | _, _ => UgFalse
  end.

Definition UgBoolFunRel
    (pR : nat -> bool) (pL : Lean.Nat -> ImportedUnitGrowth.Bool) : SProp :=
  forall nR nL, SubNatRel nR nL -> UgBoolRel (pR nR) (pL nL).

Definition ug_false_elim (P : SProp) (H : UgFalse) : P :=
  match H return P with end.

Definition ug_bool_prop_to_truth (b : bool) :
    is_true b -> UgBoolTruth b :=
  match b return is_true b -> UgBoolTruth b with
  | true => fun _ => ug_truth_intro
  | false => fun H =>
      match H in Logic.eq _ z return
        match z with true => UgFalse | false => UgTruth end
      with Logic.eq_refl => ug_truth_intro end
  end.

Lemma ug_and_intro (a b : bool) :
  is_true a -> is_true b -> is_true (a && b).
Proof. by case: a; case: b. Qed.

Definition ug_and_left (a b : bool) :
    is_true (a && b) -> is_true a :=
  match a, b return is_true (a && b) -> is_true a with
  | true, true => fun _ => Logic.eq_refl true
  | true, false => fun _ => Logic.eq_refl true
  | false, true => fun H => H
  | false, false => fun H => H
  end.

Definition ug_and_right (a b : bool) :
    is_true (a && b) -> is_true b :=
  match a, b return is_true (a && b) -> is_true b with
  | true, true => fun _ => Logic.eq_refl true
  | true, false => fun H => H
  | false, true => fun _ => Logic.eq_refl true
  | false, false => fun H => H
  end.

Definition ug_imported_false_ne_true
    (H : Lean.eq ImportedUnitGrowth.Bool_false
      ImportedUnitGrowth.Bool_true) : UgFalse :=
  match H in Lean.eq _ z return
    match z with
    | ImportedUnitGrowth.Bool_false => UgTruth
    | ImportedUnitGrowth.Bool_true => UgFalse
    end
  with Lean.eq_refl => ug_truth_intro end.

Definition ug_imported_true_ne_false
    (H : Lean.eq ImportedUnitGrowth.Bool_true
      ImportedUnitGrowth.Bool_false) : UgFalse :=
  match H in Lean.eq _ z return
    match z with
    | ImportedUnitGrowth.Bool_true => UgTruth
    | ImportedUnitGrowth.Bool_false => UgFalse
    end
  with Lean.eq_refl => ug_truth_intro end.

Lemma ug_bool_true_correspondence
    (bR : bool) (bL : ImportedUnitGrowth.Bool) :
  UgBoolRel bR bL ->
  PropSPropRel (is_true bR)
    (Lean.eq bL ImportedUnitGrowth.Bool_true).
Proof.
  intro Hrel. apply prop_sprop_rel_intro.
  - destruct bR, bL; cbn in Hrel |- *.
    + exact (ug_false_elim _ Hrel).
    + intros _. exact (@Lean.eq_refl ImportedUnitGrowth.Bool
        ImportedUnitGrowth.Bool_true).
    + intro H. exact (ug_false_elim _ (ug_bool_prop_to_truth false H)).
    + exact (ug_false_elim _ Hrel).
  - destruct bR, bL; cbn in Hrel |- *; intro Heq.
    + exact (ug_false_elim _ Hrel).
    + exact (strictly_inhabits (Logic.eq_refl true)).
    + exact (ug_false_elim _ (ug_imported_false_ne_true Heq)).
    + exact (ug_false_elim _ Hrel).
Qed.

Lemma ug_bool_false_correspondence
    (bR : bool) (bL : ImportedUnitGrowth.Bool) :
  UgBoolRel bR bL ->
  PropSPropRel (is_true (~~ bR))
    (Lean.eq bL ImportedUnitGrowth.Bool_false).
Proof.
  intro Hrel. apply prop_sprop_rel_intro.
  - destruct bR, bL; cbn in Hrel |- *.
    + exact (ug_false_elim _ Hrel).
    + intro H. exact (ug_false_elim _ (ug_bool_prop_to_truth false H)).
    + intros _. exact (@Lean.eq_refl ImportedUnitGrowth.Bool
        ImportedUnitGrowth.Bool_false).
    + exact (ug_false_elim _ Hrel).
  - destruct bR, bL; cbn in Hrel |- *; intro Heq.
    + exact (ug_false_elim _ Hrel).
    + exact (ug_false_elim _ (ug_imported_true_ne_false Heq)).
    + exact (strictly_inhabits (Logic.eq_refl true)).
    + exact (ug_false_elim _ Hrel).
Qed.

Definition ug_decide_forward (P : SProp)
    (d : ImportedUnitGrowth.Decidable P) :
    P -> Lean.eq (ImportedUnitGrowth.Decidable_decide P d)
      ImportedUnitGrowth.Bool_true :=
  match d as d0 return
      P -> Lean.eq (ImportedUnitGrowth.Decidable_decide P d0)
        ImportedUnitGrowth.Bool_true
  with
  | ImportedUnitGrowth.Decidable_isTrue H =>
      fun _ => @Lean.eq_refl ImportedUnitGrowth.Bool
        ImportedUnitGrowth.Bool_true
  | ImportedUnitGrowth.Decidable_isFalse H =>
      fun p => ug_false_elim _ (match H p return UgFalse with end)
  end.

Definition ug_decide_backward (P : SProp)
    (d : ImportedUnitGrowth.Decidable P) :
    Lean.eq (ImportedUnitGrowth.Decidable_decide P d)
      ImportedUnitGrowth.Bool_true -> P :=
  match d as d0 return
      Lean.eq (ImportedUnitGrowth.Decidable_decide P d0)
        ImportedUnitGrowth.Bool_true -> P
  with
  | ImportedUnitGrowth.Decidable_isTrue H => fun _ => H
  | ImportedUnitGrowth.Decidable_isFalse H =>
      fun Heq => ug_false_elim _ (ug_imported_false_ne_true Heq)
  end.

Lemma ug_decide_le_true_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (leq aR bR))
    (Lean.eq (ug_decide_le aL bL) ImportedUnitGrowth.Bool_true).
Proof.
  intros Ha Hb. have Hle := ug_le_correspondence _ _ _ _ Ha Hb.
  apply prop_sprop_rel_intro.
  - intro HR. apply ug_decide_forward.
    exact (prop_to_sprop _ _ Hle HR).
  - intro HL. apply strictly_inhabits.
    apply (sprop_to_prop _ _ Hle).
    exact (ug_decide_backward _ _ HL).
Qed.

Definition ug_unit_growth_target (f : Lean.Nat -> Lean.Nat) : SProp :=
  ImportedUnitGrowth.Prosa_Util_UnitGrowth_unit_growth_function f.

Lemma ug_unit_growth_correspondence
    (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat) :
  SubNatFunRel fR fL ->
  PropSPropRel
    (GeneratedUnitGrowthSource.unit_growth_function fR)
    (ug_unit_growth_target fL).
Proof.
  intro Hf. apply prop_sprop_rel_intro.
  - intros HR tL.
    set (tR := sub_nat_to_rocq tL).
    have Ht : SubNatRel tR tL := sub_nat_rel_surjective tL.
    have HleftArg := ug_add_correspondence _ _ _ _ Ht ug_one_rel.
    have Hleft := Hf _ _ HleftArg.
    have Hft := Hf _ _ Ht.
    have Hright := ug_add_correspondence _ _ _ _ Hft ug_one_rel.
    exact (prop_to_sprop _ _
      (ug_le_correspondence _ _ _ _ Hleft Hright) (HR tR)).
  - intro HL. apply strictly_inhabits. intro tR.
    have Ht := sub_nat_rel_canonical tR.
    have HleftArg := ug_add_correspondence _ _ _ _ Ht ug_one_rel.
    have Hleft := Hf _ _ HleftArg.
    have Hft := Hf _ _ Ht.
    have Hright := ug_add_correspondence _ _ _ _ Hft ug_one_rel.
    exact (sprop_to_prop _ _
      (ug_le_correspondence _ _ _ _ Hleft Hright)
      (HL (sub_nat_to_imported tR))).
Qed.

Definition ug_monotone_target (f : Lean.Nat -> Lean.Nat) : SProp :=
  ImportedUnitGrowth.Prosa_Util_Rel_monotone_inst1 Lean.Nat
    ug_decide_le f.

Lemma ug_monotone_correspondence
    (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat) :
  SubNatFunRel fR fL ->
  PropSPropRel (prosa.util.rel.monotone leq fR)
    (ug_monotone_target fL).
Proof.
  intro Hf. apply prop_sprop_rel_intro.
  - intros HR xL yL HxyL.
    set (xR := sub_nat_to_rocq xL).
    set (yR := sub_nat_to_rocq yL).
    have Hx : SubNatRel xR xL := sub_nat_rel_surjective xL.
    have Hy : SubNatRel yR yL := sub_nat_rel_surjective yL.
    have HxyR := sprop_to_prop _ _
      (ug_decide_le_true_correspondence _ _ _ _ Hx Hy) HxyL.
    have Hfx := Hf _ _ Hx.
    have Hfy := Hf _ _ Hy.
    exact (prop_to_sprop _ _
      (ug_decide_le_true_correspondence _ _ _ _ Hfx Hfy)
      (HR xR yR HxyR)).
  - intro HL. apply strictly_inhabits. intros xR yR HxyR.
    have Hx := sub_nat_rel_canonical xR.
    have Hy := sub_nat_rel_canonical yR.
    have HxyL := prop_to_sprop _ _
      (ug_decide_le_true_correspondence _ _ _ _ Hx Hy) HxyR.
    have Hfx := Hf _ _ Hx.
    have Hfy := Hf _ _ Hy.
    exact (sprop_to_prop _ _
      (ug_decide_le_true_correspondence _ _ _ _ Hfx Hfy)
      (HL _ _ HxyL)).
Qed.

Lemma ug_slowed_correspondence
    (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat) :
  SubNatFunRel fR fL ->
  SubNatFunRel (GeneratedUnitGrowthSource.slowed fR)
    (ImportedUnitGrowth.Prosa_Util_UnitGrowth_slowed fL).
Proof.
  intros Hf nR nL Hn. unfold SubNatRel in Hn.
  destruct Hn. induction nR as [|n IH].
  - cbn [GeneratedUnitGrowthSource.slowed].
    exact (sub_imported_eq_trans _ _ _
      (Hf O Lean.Nat_zero (@Lean.eq_refl Lean.Nat Lean.Nat_zero))
      (sub_imported_eq_sym _ _
        (ImportedUnitGrowth.Prosa_Util_UnitGrowth_slowed_eq_1 fL))).
  - cbn [GeneratedUnitGrowthSource.slowed sub_nat_to_imported].
    have Hfn := Hf (S n) (Lean.Nat_succ (sub_nat_to_imported n))
      (@Lean.eq_refl Lean.Nat (Lean.Nat_succ (sub_nat_to_imported n))).
    have Hstep := ug_add_correspondence _ _ _ _ IH ug_one_rel.
    have Hmin := ug_min_correspondence _ _ _ _ Hfn Hstep.
    have Hsource : Logic.eq
        (minn (fR (S n)) (GeneratedUnitGrowthSource.slowed fR n + 1))
        (minn (fR (S n)) (S (GeneratedUnitGrowthSource.slowed fR n))).
    { rewrite addn1. reflexivity. }
    have HsourceL := coq_eq_to_imported_eq _ _
      (f_equal sub_nat_to_imported Hsource).
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _ HsourceL)
      (sub_imported_eq_trans _ _ _ Hmin
        (sub_imported_eq_sym _ _
          (ImportedUnitGrowth.Prosa_Util_UnitGrowth_slowed_eq_2 fL
            (sub_nat_to_imported n))))).
Qed.

Print Assumptions ug_min_correspondence.
Print Assumptions ug_sub_correspondence.
Print Assumptions ug_decide_le_true_correspondence.
Print Assumptions ug_bool_true_correspondence.
Print Assumptions ug_bool_false_correspondence.
Print Assumptions ug_unit_growth_correspondence.
Print Assumptions ug_monotone_correspondence.
Print Assumptions ug_slowed_correspondence.
