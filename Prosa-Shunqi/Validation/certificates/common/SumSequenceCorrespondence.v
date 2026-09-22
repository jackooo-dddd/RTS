From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq fintype bigop path.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSumSequence ImportedSubadditivity.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.

(** Namespace-local realization of the already approved semantic boundaries
    for the actual [ImportedSumSequence] artifact.  lean4export seals every
    artifact in its own module, so its [List] and [Bool] carriers are distinct
    Rocq constants even though the Lean source uses the same core datatypes.
    These adapters instantiate the reusable relation pattern; they do not add
    a new representation choice. *)

Definition ss_false_elim (Q : SProp) (H : ImportedSumSequence.False) : Q :=
  match H return Q with end.

Definition ss_false_to_strict (H : ImportedSumSequence.False) :
    StrictlyInhabited Logic.False := match H with end.

Definition ss_coq_false_to_target (H : Logic.False) :
    ImportedSumSequence.False := match H return ImportedSumSequence.False with end.

Definition ss_bool_to_imported (b : bool) : ImportedSumSequence.Bool :=
  match b with
  | true => ImportedSumSequence.Bool_true
  | false => ImportedSumSequence.Bool_false
  end.

Definition ss_bool_to_rocq (b : ImportedSumSequence.Bool) : bool :=
  match b with
  | ImportedSumSequence.Bool_true => true
  | ImportedSumSequence.Bool_false => false
  end.

Definition SsBoolRel (bR : bool) (bL : ImportedSumSequence.Bool) : SProp :=
  Lean.eq (ss_bool_to_imported bR) bL.

Lemma ss_bool_source_roundtrip (b : bool) :
  Logic.eq (ss_bool_to_rocq (ss_bool_to_imported b)) b.
Proof. destruct b; reflexivity. Qed.

Lemma ss_bool_target_roundtrip (b : ImportedSumSequence.Bool) :
  Lean.eq (ss_bool_to_imported (ss_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Lemma ss_bool_true_correspondence bR bL : SsBoolRel bR bL ->
  PropSPropRel (is_true bR)
    (Lean.eq bL ImportedSumSequence.Bool_true).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Htrue. destruct bR; cbn in Htrue.
    + exact (sub_imported_eq_sym _ _ Hb).
    + discriminate Htrue.
  - intro HL. apply strictly_inhabits.
    destruct bR; cbn.
    + reflexivity.
    + exact (False_rect _ (interpret_strict Logic.False
        (ss_false_to_strict
          (ImportedSumSequence.Bool_noConfusion_inst1
            ImportedSumSequence.False ImportedSumSequence.Bool_false
            ImportedSumSequence.Bool_true
            (sub_imported_eq_trans _ _ _ Hb HL))))).
Qed.

Lemma ss_bool_eq_correspondence bR bL cR cL :
  SsBoolRel bR bL -> SsBoolRel cR cL ->
  PropSPropRel (Logic.eq bR cR) (Lean.eq bL cL).
Proof.
  intros Hb Hc. apply prop_sprop_rel_intro.
  - intro Heq. destruct Heq.
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _ Hb) Hc).
  - intro Heq. apply strictly_inhabits.
    have Hcanonical : Lean.eq (ss_bool_to_imported bR)
        (ss_bool_to_imported cR) :=
      sub_imported_eq_trans _ _ _ Hb
        (sub_imported_eq_trans _ _ _ Heq (sub_imported_eq_sym _ _ Hc)).
    have Hdecoded := f_equal ss_bool_to_rocq
      (imported_eq_to_coq_eq _ _ Hcanonical).
    rewrite (ss_bool_source_roundtrip bR) in Hdecoded.
    rewrite (ss_bool_source_roundtrip cR) in Hdecoded.
    exact Hdecoded.
Qed.

Lemma ss_bool_and_related aR aL bR bL :
  SsBoolRel aR aL -> SsBoolRel bR bL ->
  SsBoolRel (aR && bR) (ImportedSumSequence.Bool_and aL bL).
Proof.
  intros Ha Hb. unfold SsBoolRel in *.
  destruct aR, bR; cbn in *;
    exact (sub_imported_eq_congr2 ImportedSumSequence.Bool_and _ _ _ _ Ha Hb).
Qed.

Lemma ss_bool_or_related aR aL bR bL :
  SsBoolRel aR aL -> SsBoolRel bR bL ->
  SsBoolRel (aR || bR) (ImportedSumSequence.Bool_or aL bL).
Proof.
  intros Ha Hb. unfold SsBoolRel in *.
  destruct aR, bR; cbn in *;
    exact (sub_imported_eq_congr2 ImportedSumSequence.Bool_or _ _ _ _ Ha Hb).
Qed.

Lemma ss_bool_not_related bR bL :
  SsBoolRel bR bL ->
  SsBoolRel (~~ bR) (ImportedSumSequence.Bool_not bL).
Proof.
  intro Hb. unfold SsBoolRel in *.
  destruct bR; cbn in *;
    exact (sub_imported_eq_congr ImportedSumSequence.Bool_not _ _ Hb).
Qed.

Fixpoint ss_to_imported {T : Type} (xs : seq T) :
    ImportedSumSequence.List T :=
  match xs with
  | [::] => ImportedSumSequence.List_nil T
  | x :: xs' => ImportedSumSequence.List_cons T x (ss_to_imported xs')
  end.

Fixpoint ss_to_rocq {T : Type} (xs : ImportedSumSequence.List T) : seq T :=
  match xs with
  | ImportedSumSequence.List_nil => [::]
  | ImportedSumSequence.List_cons x xs' => x :: ss_to_rocq xs'
  end.

Definition SsListRel {T : Type} (xsR : seq T)
    (xsL : ImportedSumSequence.List T) : SProp :=
  Lean.eq (ss_to_imported xsR) xsL.

Lemma ss_list_source_roundtrip {T : Type} (xs : seq T) :
  Logic.eq (ss_to_rocq (ss_to_imported xs)) xs.
Proof. induction xs; cbn; first reflexivity. f_equal. exact IHxs. Qed.

Lemma ss_list_target_roundtrip {T : Type} (xs : ImportedSumSequence.List T) :
  Lean.eq (ss_to_imported (ss_to_rocq xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (@Lean.eq_refl _ (ImportedSumSequence.List_nil T)).
  - exact (sub_imported_eq_congr
      (ImportedSumSequence.List_cons T x) _ _ IH).
Qed.

Definition ss_decidable_eq (T : eqType) : ImportedSumSequence.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => ImportedSumSequence.Decidable_isTrue (Lean.eq x y)
        (coq_eq_to_imported_eq x y H)
    | ReflectF H => ImportedSumSequence.Decidable_isFalse (Lean.eq x y)
        (fun HL => ss_coq_false_to_target
          (H (imported_eq_to_coq_eq x y HL)))
    end.

Definition ss_target_mem {T : Type} (x : T)
    (xs : ImportedSumSequence.List T) : SProp :=
  ImportedSumSequence.Membership_mem T (ImportedSumSequence.List T)
    (ImportedSumSequence.List_instMembership T) xs x.

Definition ss_list_mem_transport {T : Type} (x : T)
    (xs ys : ImportedSumSequence.List T) :
    Lean.eq xs ys -> ImportedSumSequence.List_Mem T x xs ->
    ImportedSumSequence.List_Mem T x ys :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ zs return ImportedSumSequence.List_Mem T x zs with
    | Lean.eq_refl => Hmem
    end.

Definition ss_mem_head_of_coq_eq {T : Type} (x y : T)
    (xs : ImportedSumSequence.List T) : Logic.eq x y ->
    ImportedSumSequence.List_Mem T x
      (ImportedSumSequence.List_cons T y xs) :=
  fun H => match H in Logic.eq _ z return
      ImportedSumSequence.List_Mem T x
        (ImportedSumSequence.List_cons T z xs) with
    | Logic.eq_refl => ImportedSumSequence.List_Mem_head T x xs
    end.

Inductive SsTruth : SProp := ss_truth_intro.
Inductive SsFalse : SProp := .

Definition SsBoolTruth (b : bool) : SProp :=
  match b with true => SsTruth | false => SsFalse end.

Definition ss_truth_false_elim (Q : SProp) (H : SsBoolTruth false) : Q :=
  match H return Q with end.

Definition ss_prop_to_truth (b : bool) : is_true b -> SsBoolTruth b :=
  match b return is_true b -> SsBoolTruth b with
  | true => fun _ => ss_truth_intro
  | false => fun H =>
      match H in Logic.eq _ z return
        match z with true => SsFalse | false => SsTruth end
      with Logic.eq_refl => ss_truth_intro end
  end.

Definition ss_truth_to_strict_prop (b : bool) :
    SsBoolTruth b -> StrictlyInhabited (is_true b) :=
  match b return SsBoolTruth b -> StrictlyInhabited (is_true b) with
  | true => fun _ => strictly_inhabits (Logic.eq_refl true)
  | false => fun H => match H with end
  end.

Definition ss_or_left_truth (a b : bool) :
    SsBoolTruth a -> SsBoolTruth (a || b) :=
  match a, b return SsBoolTruth a -> SsBoolTruth (a || b) with
  | true, _ => fun _ => ss_truth_intro
  | false, true => fun _ => ss_truth_intro
  | false, false => fun H => H
  end.

Definition ss_or_right_truth (a b : bool) :
    SsBoolTruth b -> SsBoolTruth (a || b) :=
  match a, b return SsBoolTruth b -> SsBoolTruth (a || b) with
  | true, _ => fun _ => ss_truth_intro
  | false, true => fun _ => ss_truth_intro
  | false, false => fun H => H
  end.

Definition ss_eq_refl_truth (T : eqType) (x : T) : SsBoolTruth (x == x).
Proof. rewrite eqxx. exact ss_truth_intro. Defined.

Fixpoint ss_seq_mem_forward {T : eqType} (x : T) (xs : seq T) :
    SsBoolTruth (x \in xs) ->
    ImportedSumSequence.List_Mem T x (ss_to_imported xs) :=
  match xs as xs0 return SsBoolTruth (x \in xs0) ->
      ImportedSumSequence.List_Mem T x (ss_to_imported xs0) with
  | [::] => ss_truth_false_elim _
  | y :: ys =>
      match @eqP T x y as r in reflect _ b return
        SsBoolTruth (b || (x \in ys)) ->
        ImportedSumSequence.List_Mem T x
          (ImportedSumSequence.List_cons T y (ss_to_imported ys)) with
      | ReflectT Hxy => fun _ => ss_mem_head_of_coq_eq x y _ Hxy
      | ReflectF _ => fun H => ImportedSumSequence.List_Mem_tail T x y _
          (ss_seq_mem_forward x ys H)
      end
  end.

Fixpoint ss_imported_mem_decoded {T : eqType} (x : T)
    (xs : ImportedSumSequence.List T)
    (H : ImportedSumSequence.List_Mem T x xs) :
    SsBoolTruth (x \in ss_to_rocq xs) :=
  match H with
  | ImportedSumSequence.List_Mem_head ys =>
      ss_or_left_truth _ _ (ss_eq_refl_truth T x)
  | ImportedSumSequence.List_Mem_tail y ys Htail =>
      ss_or_right_truth _ _ (ss_imported_mem_decoded x ys Htail)
  end.

Definition ss_mem_truth_transport {T : eqType} (x : T)
    (xs ys : seq T) : Logic.eq xs ys ->
    SsBoolTruth (x \in xs) -> SsBoolTruth (x \in ys) :=
  fun H Htruth =>
    match H in Logic.eq _ zs return SsBoolTruth (x \in zs) with
    | Logic.eq_refl => Htruth
    end.

Definition ss_imported_mem_backward {T : eqType} (x : T) (xs : seq T)
    (H : ImportedSumSequence.List_Mem T x (ss_to_imported xs)) :
    SsBoolTruth (x \in xs) :=
  ss_mem_truth_transport x _ _ (ss_list_source_roundtrip xs)
    (ss_imported_mem_decoded x (ss_to_imported xs) H).

Lemma ss_membership_correspondence (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedSumSequence.List T) :
  SsListRel xsR xsL ->
  PropSPropRel (x \in xsR) (ss_target_mem x xsL).
Proof.
  intro Hlist. apply prop_sprop_rel_intro.
  - intro Hmem. unfold ss_target_mem.
    apply (ss_list_mem_transport x _ _ Hlist).
    apply ss_seq_mem_forward. exact (ss_prop_to_truth _ Hmem).
  - intro Hmem. apply ss_truth_to_strict_prop.
    apply ss_imported_mem_backward.
    unfold ss_target_mem in Hmem.
    exact (ss_list_mem_transport x _ _
      (sub_imported_eq_sym _ _ Hlist) Hmem).
Qed.

Definition SsPredRel {T : Type} (PR : T -> bool)
    (PL : T -> ImportedSumSequence.Bool) : SProp :=
  forall x, SsBoolRel (PR x) (PL x).

Definition ss_pred_to_imported {T : Type} (PR : T -> bool) :
    T -> ImportedSumSequence.Bool := fun x => ss_bool_to_imported (PR x).

Definition ss_pred_to_rocq {T : Type}
    (PL : T -> ImportedSumSequence.Bool) : T -> bool :=
  fun x => ss_bool_to_rocq (PL x).

Lemma ss_pred_canonical {T : Type} (PR : T -> bool) :
  SsPredRel PR (ss_pred_to_imported PR).
Proof. intro x. exact (@Lean.eq_refl _ _). Qed.

Lemma ss_pred_surjective {T : Type}
    (PL : T -> ImportedSumSequence.Bool) :
  SsPredRel (ss_pred_to_rocq PL) PL.
Proof. intro x. exact (ss_bool_target_roundtrip (PL x)). Qed.

Definition SsNatFunRel {T : Type} (FR : T -> nat)
    (FL : T -> Lean.Nat) : SProp :=
  forall x, SubNatRel (FR x) (FL x).

Definition ss_nat_fun_to_imported {T : Type} (FR : T -> nat) :
    T -> Lean.Nat := fun x => sub_nat_to_imported (FR x).

Definition ss_nat_fun_to_rocq {T : Type} (FL : T -> Lean.Nat) :
    T -> nat := fun x => sub_nat_to_rocq (FL x).

Lemma ss_nat_fun_canonical {T : Type} (FR : T -> nat) :
  SsNatFunRel FR (ss_nat_fun_to_imported FR).
Proof. intro x. exact (sub_nat_rel_canonical (FR x)). Qed.

Lemma ss_nat_fun_surjective {T : Type} (FL : T -> Lean.Nat) :
  SsNatFunRel (ss_nat_fun_to_rocq FL) FL.
Proof. intro x. exact (sub_nat_rel_surjective (FL x)). Qed.

(** Target arithmetic aliases are definitionally the actual typeclass-resolved
    operations found in the imported theorem types. *)
Definition ss_target_zero : Lean.Nat :=
  ImportedSumSequence.OfNat_ofNat_inst1 Lean.Nat Lean.Nat_zero
    (ImportedSumSequence.instOfNatNat Lean.Nat_zero).

Definition ss_target_add (a b : Lean.Nat) : Lean.Nat :=
  ImportedSumSequence.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedSumSequence.instHAdd_inst1 Lean.Nat
      ImportedSumSequence.instAddNat) a b.

Definition ss_target_mul (a b : Lean.Nat) : Lean.Nat :=
  ImportedSumSequence.HMul_hMul_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedSumSequence.instHMul_inst1 Lean.Nat
      ImportedSumSequence.instMulNat) a b.

Definition ss_target_le (a b : Lean.Nat) : SProp :=
  ImportedSumSequence.LE_le_inst1 Lean.Nat ImportedSumSequence.instLENat a b.

Definition ss_target_lt (a b : Lean.Nat) : SProp :=
  ImportedSumSequence.LT_lt_inst1 Lean.Nat ImportedSumSequence.instLTNat a b.

Lemma ss_zero_related : SubNatRel 0 ss_target_zero.
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma ss_add_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR + bR) (ss_target_add aL bL).
Proof. exact (sub_add_correspondence aR aL bR bL). Qed.

Lemma ss_mul_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR * bR) (ss_target_mul aL bL).
Proof. exact (sub_mul_correspondence aR aL bR bL). Qed.

Lemma ss_le_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (leq aR bR)) (ss_target_le aL bL).
Proof. exact (sub_nat_le_correspondence aR aL bR bL). Qed.

Lemma ss_lt_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (ltn aR bR)) (ss_target_lt aL bL).
Proof. exact (sub_nat_lt_correspondence aR aL bR bL). Qed.

Definition ss_target_decide_nat_eq (a b : Lean.Nat) :
    ImportedSumSequence.Bool :=
  ImportedSumSequence.Decidable_decide (Lean.eq a b)
    (ImportedSumSequence.instDecidableEqNat a b).

Lemma ss_decide_bool_correspondence (b : bool) (Q : SProp)
    (d : ImportedSumSequence.Decidable Q) :
  PropSPropRel (is_true b) Q ->
  SsBoolRel b (ImportedSumSequence.Decidable_decide Q d).
Proof.
  intro Hrel. unfold SsBoolRel.
  destruct d as [Hfalse | Htrue]; destruct b; cbn.
  - exact (ss_false_elim _
      (Hfalse (prop_to_sprop _ _ Hrel (Logic.eq_refl true)))).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - exact (ss_false_elim _ (ss_coq_false_to_target
      (match sprop_to_prop _ _ Hrel Htrue with end))).
Qed.

Lemma ss_decide_nat_eq_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SsBoolRel (aR == bR) (ss_target_decide_nat_eq aL bL).
Proof.
  intros Ha Hb. apply ss_decide_bool_correspondence.
  apply prop_sprop_rel_intro.
  - intro Hbool. apply (prop_to_sprop _ _
      (sub_nat_eq_correspondence aR aL bR bL Ha Hb)).
    by move/eqP: Hbool.
  - intro Heq. apply strictly_inhabits. apply/eqP.
    exact (sprop_to_prop _ _
      (sub_nat_eq_correspondence aR aL bR bL Ha Hb) Heq).
Qed.

Definition ss_target_decide_lt (a b : Lean.Nat) :
    ImportedSumSequence.Bool :=
  ImportedSumSequence.Decidable_decide (ss_target_lt a b)
    (ImportedSumSequence.Nat_decLt a b).

Lemma ss_decide_lt_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SsBoolRel (ltn aR bR) (ss_target_decide_lt aL bL).
Proof.
  intros Ha Hb. apply ss_decide_bool_correspondence.
  exact (ss_lt_correspondence aR aL bR bL Ha Hb).
Qed.

Definition ss_target_decide_le (a b : Lean.Nat) :
    ImportedSumSequence.Bool :=
  ImportedSumSequence.Decidable_decide (ss_target_le a b)
    (ImportedSumSequence.Nat_decLe a b).

Lemma ss_decide_le_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SsBoolRel (leq aR bR) (ss_target_decide_le aL bL).
Proof.
  intros Ha Hb. apply ss_decide_bool_correspondence.
  exact (ss_le_correspondence aR aL bR bL Ha Hb).
Qed.

Lemma ss_decide_le_true_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (leq aR bR))
    (Lean.eq (ss_target_decide_le aL bL)
      ImportedSumSequence.Bool_true).
Proof.
  intros Ha Hb. apply ss_bool_true_correspondence.
  exact (ss_decide_le_related aR aL bR bL Ha Hb).
Qed.

Definition ss_target_decide_bool_true (b : ImportedSumSequence.Bool) :
    ImportedSumSequence.Bool :=
  ImportedSumSequence.Decidable_decide
    (Lean.eq b ImportedSumSequence.Bool_true)
    (ImportedSumSequence.instDecidableEqBool b
      ImportedSumSequence.Bool_true).

Lemma ss_decide_bool_true_related bR bL :
  SsBoolRel bR bL -> SsBoolRel bR (ss_target_decide_bool_true bL).
Proof.
  intro Hb. apply ss_decide_bool_correspondence.
  exact (ss_bool_true_correspondence bR bL Hb).
Qed.

Definition ss_target_decide_eq (T : eqType) (x y : T) :
    ImportedSumSequence.Bool :=
  ImportedSumSequence.Decidable_decide (Lean.eq x y) (ss_decidable_eq T x y).

Lemma ss_decide_eq_related (T : eqType) (x y : T) :
  SsBoolRel (x == y) (ss_target_decide_eq T x y).
Proof.
  apply ss_decide_bool_correspondence.
  apply prop_sprop_rel_intro.
  - intro Hxy. move/eqP: Hxy => Hxy.
    exact (coq_eq_to_imported_eq x y Hxy).
  - intro Hxy. apply strictly_inhabits. apply/eqP.
    exact (imported_eq_to_coq_eq x y Hxy).
Qed.

Definition ss_target_ne (T : Type) (x y : T) : SProp :=
  ImportedSumSequence.Ne T x y.

Definition ss_target_decide_ne (T : eqType) (x y : T) :
    ImportedSumSequence.Bool :=
  ImportedSumSequence.Decidable_decide (ss_target_ne T x y)
    (ImportedSumSequence.instDecidableNot (Lean.eq x y) (ss_decidable_eq T x y)).

Lemma ss_decide_ne_related (T : eqType) (x y : T) :
  SsBoolRel (x != y) (ss_target_decide_ne T x y).
Proof.
  apply ss_decide_bool_correspondence.
  apply prop_sprop_rel_intro.
  - intros Hne Hxy. move/negP: Hne => Hne.
    apply ss_coq_false_to_target. apply Hne. apply/eqP.
    exact (imported_eq_to_coq_eq x y Hxy).
  - intro Hne. apply strictly_inhabits. apply/negP. intro Hxy.
    exact (interpret_strict Logic.False
      (ss_false_to_strict (Hne (coq_eq_to_imported_eq x y
        (elimT eqP Hxy))))).
Qed.

(** Ordered sequence operations. *)
Definition ss_target_filter {T : Type}
    (P : T -> ImportedSumSequence.Bool) (xs : ImportedSumSequence.List T) :
    ImportedSumSequence.List T := ImportedSumSequence.List_filter T P xs.

Definition ss_filter_match {T : Type} (b : ImportedSumSequence.Bool)
    (x : T) (tail : ImportedSumSequence.List T) :
    ImportedSumSequence.List T :=
  ImportedSumSequence.Prosa_Validation_SumSequenceInterface_generic_filter_cons_match_1
    (fun _ : ImportedSumSequence.Bool => ImportedSumSequence.List T) b
    (fun _ : ImportedSumSequence.Unit =>
      ImportedSumSequence.List_cons T x tail)
    (fun _ : ImportedSumSequence.Unit => tail).

Lemma ss_filter_match_canonical {T : Type} (b : bool) (x : T)
    (tail : ImportedSumSequence.List T) :
  Lean.eq (ss_filter_match (ss_bool_to_imported b) x tail)
    (match b with
     | true => ImportedSumSequence.List_cons T x tail
     | false => tail
     end).
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Lemma ss_filter_branch_canonical {T : Type} (b : bool) (x : T)
    (filtered : seq T) (tail : ImportedSumSequence.List T) :
  Lean.eq tail (ss_to_imported filtered) ->
  Lean.eq
    (match b with
     | true => ImportedSumSequence.List_cons T x tail
     | false => tail
     end)
    (ss_to_imported
      (match b with true => x :: filtered | false => filtered end)).
Proof.
  intro IH. destruct b; cbn.
  - exact (sub_imported_eq_congr (ImportedSumSequence.List_cons T x) _ _ IH).
  - exact IH.
Qed.

Lemma ss_source_filter_cons {T : Type} (P : T -> bool)
    (x : T) (xs : seq T) :
  Logic.eq
    (match P x with
     | true => x :: [seq y <- xs | P y]
     | false => [seq y <- xs | P y]
     end)
    [seq y <- x :: xs | P y].
Proof. cbn. destruct (P x); reflexivity. Qed.

Lemma ss_filter_canonical (T : Type) (PR : T -> bool)
    (PL : T -> ImportedSumSequence.Bool) : SsPredRel PR PL ->
  forall xs : seq T,
  Lean.eq (ss_target_filter PL (ss_to_imported xs))
    (ss_to_imported [seq x <- xs | PR x]).
Proof.
  intro HP. induction xs as [|x xs IH].
  - exact
      (ImportedSumSequence.Prosa_Validation_SumSequenceInterface_generic_filter_nil
        T PL).
  - refine (sub_imported_eq_trans _ _ _
      (ImportedSumSequence.Prosa_Validation_SumSequenceInterface_generic_filter_cons
        T PL x (ss_to_imported xs)) _).
    refine (sub_imported_eq_trans _ _ _
      (sub_imported_eq_congr
        (fun b => ss_filter_match b x
          (ss_target_filter PL (ss_to_imported xs))) _ _
        (sub_imported_eq_sym _ _ (HP x))) _).
    refine (sub_imported_eq_trans _ _ _
      (ss_filter_match_canonical (PR x) x
        (ss_target_filter PL (ss_to_imported xs))) _).
    refine (sub_imported_eq_trans _ _ _
      (ss_filter_branch_canonical (PR x) x
        [seq y <- xs | PR y]
        (ss_target_filter PL (ss_to_imported xs)) IH) _).
    exact (coq_eq_to_imported_eq _ _
      (f_equal ss_to_imported (ss_source_filter_cons PR x xs))).
Qed.

Lemma ss_filter_related (T : Type) (PR : T -> bool)
    (PL : T -> ImportedSumSequence.Bool) (xsR : seq T)
    (xsL : ImportedSumSequence.List T) :
  SsPredRel PR PL -> SsListRel xsR xsL ->
  SsListRel [seq x <- xsR | PR x] (ss_target_filter PL xsL).
Proof.
  intros HP Hxs. unfold SsListRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (ss_filter_canonical T PR PL HP xsR))
    (sub_imported_eq_congr (ss_target_filter PL) _ _ Hxs)).
Qed.

Definition ss_target_length {T : Type}
    (xs : ImportedSumSequence.List T) : Lean.Nat :=
  ImportedSumSequence.List_length T xs.

Lemma ss_length_canonical (T : Type) (xs : seq T) :
  SubNatRel (size xs) (ss_target_length (ss_to_imported xs)).
Proof.
  induction xs as [|x xs IH].
  - exact (sub_imported_eq_trans _ _ _ ss_zero_related
      (sub_imported_eq_sym _ _
        (ImportedSumSequence.Prosa_Validation_SumSequenceInterface_generic_length_nil
          T))).
  - unfold SubNatRel in IH |- *.
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_congr Lean.Nat_succ _ _ IH)
      (sub_imported_eq_sym _ _
        (ImportedSumSequence.Prosa_Validation_SumSequenceInterface_generic_length_cons
          T x (ss_to_imported xs)))).
Qed.

Lemma ss_length_related (T : Type) (xsR : seq T)
    (xsL : ImportedSumSequence.List T) : SsListRel xsR xsL ->
  SubNatRel (size xsR) (ss_target_length xsL).
Proof.
  intro Hxs. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _ (ss_length_canonical T xsR)
    (sub_imported_eq_congr ss_target_length _ _ Hxs)).
Qed.

Definition ss_target_all {T : Type} (xs : ImportedSumSequence.List T)
    (P : T -> ImportedSumSequence.Bool) : ImportedSumSequence.Bool :=
  ImportedSumSequence.List_all T xs P.

Definition ss_target_any {T : Type} (xs : ImportedSumSequence.List T)
    (P : T -> ImportedSumSequence.Bool) : ImportedSumSequence.Bool :=
  ImportedSumSequence.List_any T xs P.

Definition ss_target_isEmpty {T : Type}
    (xs : ImportedSumSequence.List T) : ImportedSumSequence.Bool :=
  ImportedSumSequence.List_isEmpty T xs.

Fixpoint ss_all_canonical (T : Type) (PR : T -> bool)
    (PL : T -> ImportedSumSequence.Bool) (xs : seq T) :
  SsPredRel PR PL ->
  SsBoolRel (all PR xs) (ss_target_all (ss_to_imported xs) PL).
Proof.
  intro HP. destruct xs as [|x xs].
  - exact (sub_imported_eq_sym _ _
      (ImportedSumSequence.Prosa_Validation_SumSequenceInterface_generic_all_nil
        T PL)).
  - exact (sub_imported_eq_trans _ _ _
      (ss_bool_and_related _ _ _ _ (HP x)
        (ss_all_canonical T PR PL xs HP))
      (sub_imported_eq_sym _ _
        (ImportedSumSequence.Prosa_Validation_SumSequenceInterface_generic_all_cons
          T PL x (ss_to_imported xs)))).
Defined.

Lemma ss_all_related (T : Type) (PR : T -> bool)
    (PL : T -> ImportedSumSequence.Bool) (xsR : seq T)
    (xsL : ImportedSumSequence.List T) :
  SsPredRel PR PL -> SsListRel xsR xsL ->
  SsBoolRel (all PR xsR) (ss_target_all xsL PL).
Proof.
  intros HP Hxs. unfold SsListRel in Hxs. unfold SsBoolRel.
  exact (sub_imported_eq_trans _ _ _ (ss_all_canonical T PR PL xsR HP)
    (sub_imported_eq_congr (fun zs => ss_target_all zs PL) _ _ Hxs)).
Qed.

Fixpoint ss_any_canonical (T : Type) (PR : T -> bool)
    (PL : T -> ImportedSumSequence.Bool) (xs : seq T) :
  SsPredRel PR PL ->
  SsBoolRel (has PR xs) (ss_target_any (ss_to_imported xs) PL).
Proof.
  intro HP. destruct xs as [|x xs].
  - exact (sub_imported_eq_sym _ _
      (ImportedSumSequence.Prosa_Validation_SumSequenceInterface_generic_any_nil
        T PL)).
  - exact (sub_imported_eq_trans _ _ _
      (ss_bool_or_related _ _ _ _ (HP x)
        (ss_any_canonical T PR PL xs HP))
      (sub_imported_eq_sym _ _
        (ImportedSumSequence.Prosa_Validation_SumSequenceInterface_generic_any_cons
          T PL x (ss_to_imported xs)))).
Defined.

Lemma ss_any_related (T : Type) (PR : T -> bool)
    (PL : T -> ImportedSumSequence.Bool) (xsR : seq T)
    (xsL : ImportedSumSequence.List T) :
  SsPredRel PR PL -> SsListRel xsR xsL ->
  SsBoolRel (has PR xsR) (ss_target_any xsL PL).
Proof.
  intros HP Hxs. unfold SsListRel in Hxs. unfold SsBoolRel.
  exact (sub_imported_eq_trans _ _ _ (ss_any_canonical T PR PL xsR HP)
    (sub_imported_eq_congr (fun zs => ss_target_any zs PL) _ _ Hxs)).
Qed.

Lemma ss_source_all_filter_imp (T : Type) (P Q : T -> bool)
    (xs : seq T) :
  Logic.eq (all Q [seq x <- xs | P x])
    (all (fun x => ~~ P x || Q x) xs).
Proof.
  have Hpred : forall x, (P x ==> Q x) = (~~ P x || Q x).
  { intro x. by case: (P x); case: (Q x). }
  exact (Logic.eq_trans (all_filter Q P xs) (eq_all Hpred xs)).
Qed.

Lemma ss_source_has_filter_and (T : Type) (P Q : T -> bool)
    (xs : seq T) :
  Logic.eq (has Q [seq x <- xs | P x])
    (has (fun x => P x && Q x) xs).
Proof.
  have Hpred : forall x, (Q x && P x) = (P x && Q x).
  { intro x. exact (andbC (Q x) (P x)). }
  have Hcount := eq_count Hpred xs.
  change (has Q (filter P xs) =
    has (fun x => P x && Q x) xs).
  rewrite !has_count count_filter Hcount. reflexivity.
Qed.

Lemma ss_all_filter_imp_related (T : Type)
    (PR QR : T -> bool)
    (PL QL : T -> ImportedSumSequence.Bool)
    (xsR : seq T) (xsL : ImportedSumSequence.List T) :
  SsPredRel PR PL -> SsPredRel QR QL -> SsListRel xsR xsL ->
  SsBoolRel (all QR [seq x <- xsR | PR x])
    (ss_target_all xsL
      (fun x => ImportedSumSequence.Bool_or
        (ImportedSumSequence.Bool_not (PL x)) (QL x))).
Proof.
  intros HP HQ Hxs.
  have Hpred : SsPredRel (fun x => ~~ PR x || QR x)
      (fun x => ImportedSumSequence.Bool_or
        (ImportedSumSequence.Bool_not (PL x)) (QL x)) :=
    fun x => ss_bool_or_related _ _ _ _
      (ss_bool_not_related _ _ (HP x)) (HQ x).
  rewrite (ss_source_all_filter_imp T PR QR xsR).
  exact (ss_all_related T _ _ xsR xsL Hpred Hxs).
Qed.

Lemma ss_any_filter_and_related (T : Type)
    (PR QR : T -> bool)
    (PL QL : T -> ImportedSumSequence.Bool)
    (xsR : seq T) (xsL : ImportedSumSequence.List T) :
  SsPredRel PR PL -> SsPredRel QR QL -> SsListRel xsR xsL ->
  SsBoolRel (has QR [seq x <- xsR | PR x])
    (ss_target_any xsL
      (fun x => ImportedSumSequence.Bool_and (PL x) (QL x))).
Proof.
  intros HP HQ Hxs.
  have Hpred : SsPredRel (fun x => PR x && QR x)
      (fun x => ImportedSumSequence.Bool_and (PL x) (QL x)) :=
    fun x => ss_bool_and_related _ _ _ _ (HP x) (HQ x).
  rewrite (ss_source_has_filter_and T PR QR xsR).
  exact (ss_any_related T _ _ xsR xsL Hpred Hxs).
Qed.

Lemma ss_isEmpty_canonical (T : Type) (xs : seq T) :
  SsBoolRel (nilp xs) (ss_target_isEmpty (ss_to_imported xs)).
Proof.
  destruct xs as [|x xs].
  - exact (sub_imported_eq_sym _ _
      (ImportedSumSequence.Prosa_Validation_SumSequenceInterface_generic_isEmpty_nil
        T)).
  - exact (sub_imported_eq_sym _ _
      (ImportedSumSequence.Prosa_Validation_SumSequenceInterface_generic_isEmpty_cons
        T x (ss_to_imported xs))).
Qed.

(** Sequence sums preserve ordering and multiplicity. *)
Definition ss_target_sumSeq {T : Type}
    (xs : ImportedSumSequence.List T) (F : T -> Lean.Nat) : Lean.Nat :=
  ImportedSumSequence.Prosa_Util_Sum_sumSeq T xs F.

Fixpoint ss_sumSeq_canonical (T : Type) (FR : T -> nat)
    (FL : T -> Lean.Nat) (xs : seq T) : SsNatFunRel FR FL ->
  SubNatRel (\sum_(x <- xs) FR x)
    (ss_target_sumSeq (ss_to_imported xs) FL).
Proof.
  intro HF. destruct xs as [|x xs].
  - rewrite big_nil. exact (sub_imported_eq_trans _ _ _ ss_zero_related
      (sub_imported_eq_sym _ _
        (ImportedSumSequence.Prosa_Validation_SumSequenceInterface_production_sumSeq_nil
          T FL))).
  - rewrite big_cons. exact (sub_imported_eq_trans _ _ _
      (ss_add_related (FR x) (FL x) (\sum_(i <- xs) FR i)
        (ss_target_sumSeq (ss_to_imported xs) FL)
        (HF x) (ss_sumSeq_canonical T FR FL xs HF))
      (sub_imported_eq_sym _ _
        (ImportedSumSequence.Prosa_Validation_SumSequenceInterface_production_sumSeq_cons
          T x (ss_to_imported xs) FL))).
Defined.

Lemma ss_sumSeq_related (T : Type) (FR : T -> nat)
    (FL : T -> Lean.Nat) (xsR : seq T)
    (xsL : ImportedSumSequence.List T) :
  SsNatFunRel FR FL -> SsListRel xsR xsL ->
  SubNatRel (\sum_(x <- xsR) FR x) (ss_target_sumSeq xsL FL).
Proof.
  intros HF Hxs. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _ (ss_sumSeq_canonical T FR FL xsR HF)
    (sub_imported_eq_congr (fun zs => ss_target_sumSeq zs FL) _ _ Hxs)).
Qed.

Definition ss_target_sumFiltered {T : Type}
    (xs : ImportedSumSequence.List T)
    (P : T -> ImportedSumSequence.Bool) (F : T -> Lean.Nat) : Lean.Nat :=
  ImportedSumSequence.Prosa_Util_Sum_sumFiltered T xs P F.

Lemma ss_target_sumFiltered_as_sumSeq (T : Type)
    (xs : ImportedSumSequence.List T)
    (P : T -> ImportedSumSequence.Bool) (F : T -> Lean.Nat) :
  Lean.eq (ss_target_sumFiltered xs P F)
    (ss_target_sumSeq (ss_target_filter P xs) F).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma ss_filtered_bigop_as_filter (T : Type) (P : T -> bool)
    (F : T -> nat) (xs : seq T) :
  Logic.eq (\sum_(x <- xs | P x) F x)
    (\sum_(x <- [seq y <- xs | P y]) F x).
Proof. by rewrite big_filter. Qed.

Lemma ss_sumFiltered_related (T : Type) (PR : T -> bool)
    (PL : T -> ImportedSumSequence.Bool)
    (FR : T -> nat) (FL : T -> Lean.Nat)
    (xsR : seq T) (xsL : ImportedSumSequence.List T) :
  SsPredRel PR PL -> SsNatFunRel FR FL -> SsListRel xsR xsL ->
  SubNatRel (\sum_(x <- xsR | PR x) FR x)
    (ss_target_sumFiltered xsL PL FL).
Proof.
  intros HP HF Hxs.
  have Hfilter := ss_filter_related T PR PL xsR xsL HP Hxs.
  have Hsum := ss_sumSeq_related T FR FL
    [seq y <- xsR | PR y] (ss_target_filter PL xsL) HF Hfilter.
  unfold SubNatRel in Hsum |- *.
  rewrite (ss_filtered_bigop_as_filter T PR FR xsR).
  exact (sub_imported_eq_trans _ _ _ Hsum
    (sub_imported_eq_sym _ _ (ss_target_sumFiltered_as_sumSeq T xsL PL FL))).
Qed.

(** Filtered maximum, using the actual imported [Nat.max] and fold body. *)
Definition ss_target_max (a b : Lean.Nat) : Lean.Nat :=
  ImportedSumSequence.Max_max_inst1 Lean.Nat
    ImportedSumSequence.Nat_instMax a b.

Lemma ss_target_max_canonical (a b : nat) :
  Lean.eq
    (ss_target_max (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (maxn a b)).
Proof.
  unfold ss_target_max, ImportedSumSequence.Max_max_inst1,
    ImportedSumSequence.Nat_instMax,
    ImportedSumSequence.maxOfLe_inst1.
  cbn.
  destruct (ImportedSumSequence.Nat_decLe
    (sub_nat_to_imported a) (sub_nat_to_imported b)) as [Hnle|Hle].
  - have Hrel := sub_nat_le_correspondence a (sub_nat_to_imported a)
      b (sub_nat_to_imported b) (sub_nat_rel_canonical a)
      (sub_nat_rel_canonical b).
    have Hnot : ~ is_true (leq a b).
    { intro Hab. exact (interpret_strict Logic.False
        (ss_false_to_strict (Hnle (prop_to_sprop _ _ Hrel Hab)))). }
    have Hba : is_true (leq b a).
    { move: (leq_total a b) => /orP [Hab|Hba]; last exact Hba.
      exfalso. exact (Hnot Hab). }
    have Hmax : maxn a b = a := (elimT maxn_idPl Hba).
    rewrite Hmax. exact (@Lean.eq_refl _ _).
  - have Hab : is_true (leq a b) := sprop_to_prop _ _
      (sub_nat_le_correspondence a (sub_nat_to_imported a)
        b (sub_nat_to_imported b) (sub_nat_rel_canonical a)
        (sub_nat_rel_canonical b)) Hle.
    have Hmax : maxn a b = b := (elimT maxn_idPr Hab).
    rewrite Hmax. exact (@Lean.eq_refl _ _).
Qed.

Lemma ss_max_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (maxn aR bR) (ss_target_max aL bL).
Proof.
  intros Ha Hb. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (ss_target_max_canonical aR bR))
    (sub_imported_eq_congr2 ss_target_max _ _ _ _ Ha Hb)).
Qed.

Definition ss_target_maxFiltered {T : Type}
    (xs : ImportedSumSequence.List T)
    (P : T -> ImportedSumSequence.Bool) (F : T -> Lean.Nat) : Lean.Nat :=
  ImportedSumSequence.Prosa_Util_Sum_maxFiltered T xs P F.

Fixpoint ss_maxFiltered_canonical (T : Type) (PR : T -> bool)
    (PL : T -> ImportedSumSequence.Bool)
    (FR : T -> nat) (FL : T -> Lean.Nat) (xs : seq T) :
  SsPredRel PR PL -> SsNatFunRel FR FL ->
  SubNatRel (\max_(x <- xs | PR x) FR x)
    (ss_target_maxFiltered (ss_to_imported xs) PL FL).
Proof.
  intros HP HF. destruct xs as [|x xs].
  - rewrite big_nil. exact (sub_imported_eq_trans _ _ _ ss_zero_related
      (sub_imported_eq_sym _ _
        (ImportedSumSequence.Prosa_Validation_SumSequenceInterface_production_maxFiltered_nil
          T PL FL))).
  - rewrite big_cons. destruct (PR x) eqn:Hpx.
    + cbn. have Htail := ss_maxFiltered_canonical T PR PL FR FL xs HP HF.
      have Hmax := ss_max_related (FR x) (FL x)
        (\max_(i <- xs | PR i) FR i)
        (ss_target_maxFiltered (ss_to_imported xs) PL FL) (HF x) Htail.
      have HPx0 := HP x. rewrite Hpx in HPx0.
      have HPx : Lean.eq (PL x) ImportedSumSequence.Bool_true :=
        sub_imported_eq_sym _ _ HPx0.
      exact (sub_imported_eq_trans _ _ _ Hmax
        (sub_imported_eq_trans _ _ _
          (sub_imported_eq_congr
            (fun b =>
              ImportedSumSequence.Prosa_Validation_SumSequenceInterface_generic_filter_cons_match_1
                (fun _ : ImportedSumSequence.Bool => Lean.Nat) b
                (fun _ : ImportedSumSequence.Unit =>
                  ss_target_max (FL x)
                    (ss_target_maxFiltered (ss_to_imported xs) PL FL))
                (fun _ : ImportedSumSequence.Unit =>
                  ss_target_maxFiltered (ss_to_imported xs) PL FL))
            _ _ (sub_imported_eq_sym _ _ HPx))
          (sub_imported_eq_sym _ _
            (ImportedSumSequence.Prosa_Validation_SumSequenceInterface_production_maxFiltered_cons
              T x (ss_to_imported xs) PL FL)))).
    + cbn. have Htail := ss_maxFiltered_canonical T PR PL FR FL xs HP HF.
      have HPx0 := HP x. rewrite Hpx in HPx0.
      have HPx : Lean.eq (PL x) ImportedSumSequence.Bool_false :=
        sub_imported_eq_sym _ _ HPx0.
      exact (sub_imported_eq_trans _ _ _ Htail
        (sub_imported_eq_trans _ _ _
          (sub_imported_eq_congr
            (fun b =>
              ImportedSumSequence.Prosa_Validation_SumSequenceInterface_generic_filter_cons_match_1
                (fun _ : ImportedSumSequence.Bool => Lean.Nat) b
                (fun _ : ImportedSumSequence.Unit =>
                  ss_target_max (FL x)
                    (ss_target_maxFiltered (ss_to_imported xs) PL FL))
                (fun _ : ImportedSumSequence.Unit =>
                  ss_target_maxFiltered (ss_to_imported xs) PL FL))
            _ _ (sub_imported_eq_sym _ _ HPx))
          (sub_imported_eq_sym _ _
            (ImportedSumSequence.Prosa_Validation_SumSequenceInterface_production_maxFiltered_cons
              T x (ss_to_imported xs) PL FL)))).
Defined.

Lemma ss_maxFiltered_related (T : Type) (PR : T -> bool)
    (PL : T -> ImportedSumSequence.Bool)
    (FR : T -> nat) (FL : T -> Lean.Nat)
    (xsR : seq T) (xsL : ImportedSumSequence.List T) :
  SsPredRel PR PL -> SsNatFunRel FR FL -> SsListRel xsR xsL ->
  SubNatRel (\max_(x <- xsR | PR x) FR x)
    (ss_target_maxFiltered xsL PL FL).
Proof.
  intros HP HF Hxs. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (ss_maxFiltered_canonical T PR PL FR FL xsR HP HF)
    (sub_imported_eq_congr (fun zs => ss_target_maxFiltered zs PL FL)
      _ _ Hxs)).
Qed.

(** The Boolean subsequence computation.  The actual Lean body compiles via
    [List.brecOn]; the three exported `rfl` equations below are the only
    interface used here. *)
Definition ss_target_subseqb (T : eqType)
    (xs ys : ImportedSumSequence.List T) : ImportedSumSequence.Bool :=
  ImportedSumSequence.Prosa_Util_Sum_subseqb T (ss_decidable_eq T) xs ys.

Definition ss_target_eq_ite (T : eqType) (x y : T)
    (a b : ImportedSumSequence.Bool) : ImportedSumSequence.Bool :=
  ImportedSumSequence.ite ImportedSumSequence.Bool (Lean.eq x y)
    (ss_decidable_eq T x y) a b.

Lemma ss_target_eq_ite_true (T : eqType) (x y : T)
    (a b : ImportedSumSequence.Bool) : Logic.eq x y ->
  Lean.eq (ss_target_eq_ite T x y a b) a.
Proof.
  intro Heq. subst y. unfold ss_target_eq_ite, ss_decidable_eq.
  destruct (@eqP T x x) as [Heq | Hneq].
  - exact (@Lean.eq_refl _ _).
  - exfalso. exact (Hneq (Logic.eq_refl x)).
Qed.

Lemma ss_target_eq_ite_false (T : eqType) (x y : T)
    (a b : ImportedSumSequence.Bool) : (Logic.eq x y -> Logic.False) ->
  Lean.eq (ss_target_eq_ite T x y a b) b.
Proof.
  intro Hneq. unfold ss_target_eq_ite, ss_decidable_eq.
  destruct (@eqP T x y) as [Heq | Hne].
  - exfalso. exact (Hneq Heq).
  - exact (@Lean.eq_refl _ _).
Qed.

Lemma ss_source_subseq_nil (T : eqType) (xs : seq T) :
  Logic.eq (subseq xs [::]) (nilp xs).
Proof. by case: xs. Qed.

Lemma ss_source_subseq_nil_cons (T : eqType) (y : T) (ys : seq T) :
  Logic.eq (subseq [::] (y :: ys)) true.
Proof. reflexivity. Qed.

Lemma ss_source_subseq_cons_cons (T : eqType)
    (x : T) (xs : seq T) (y : T) (ys : seq T) :
  Logic.eq (subseq (x :: xs) (y :: ys))
    (if x == y then subseq xs ys else subseq (x :: xs) ys).
Proof. by rewrite /=; case: (x == y). Qed.

Fixpoint ss_subseqb_canonical (T : eqType) (ys : seq T) :
  forall xs : seq T,
  SsBoolRel (subseq xs ys)
    (ss_target_subseqb T (ss_to_imported xs) (ss_to_imported ys)).
Proof.
  destruct ys as [|y ys]; intro xs.
  - rewrite (ss_source_subseq_nil T xs).
    exact (sub_imported_eq_trans _ _ _ (ss_isEmpty_canonical T xs)
      (sub_imported_eq_sym _ _
        (ImportedSumSequence.Prosa_Validation_SumSequenceInterface_production_subseqb_nil_right
          T (ss_decidable_eq T) (ss_to_imported xs)))).
  - destruct xs as [|x xs].
    + rewrite (ss_source_subseq_nil_cons T y ys).
      exact (sub_imported_eq_sym _ _
        (ImportedSumSequence.Prosa_Validation_SumSequenceInterface_production_subseqb_nil_left_cons
          T (ss_decidable_eq T) y (ss_to_imported ys))).
    + rewrite (ss_source_subseq_cons_cons T x xs y ys).
      have Heq :=
        ImportedSumSequence.Prosa_Validation_SumSequenceInterface_production_subseqb_cons_cons
          T (ss_decidable_eq T) x (ss_to_imported xs) y
          (ss_to_imported ys).
      destruct (@eqP T x y) as [Hxy | Hxy].
      * subst x.
        have Hbranch := ss_target_eq_ite_true T y y
          (ss_target_subseqb T (ss_to_imported xs) (ss_to_imported ys))
          (ss_target_subseqb T
            (ImportedSumSequence.List_cons T y (ss_to_imported xs))
            (ss_to_imported ys)) (Logic.eq_refl y).
        exact (sub_imported_eq_trans _ _ _
          (ss_subseqb_canonical T ys xs)
          (sub_imported_eq_trans _ _ _
            (sub_imported_eq_sym _ _ Hbranch)
            (sub_imported_eq_sym _ _ Heq))).
      *
        have Hbranch := ss_target_eq_ite_false T x y
          (ss_target_subseqb T (ss_to_imported xs) (ss_to_imported ys))
          (ss_target_subseqb T
            (ImportedSumSequence.List_cons T x (ss_to_imported xs))
            (ss_to_imported ys)) Hxy.
        exact (sub_imported_eq_trans _ _ _
          (ss_subseqb_canonical T ys (x :: xs))
          (sub_imported_eq_trans _ _ _
            (sub_imported_eq_sym _ _ Hbranch)
            (sub_imported_eq_sym _ _ Heq))).
Defined.

Lemma ss_subseqb_related (T : eqType) (xsR ysR : seq T)
    (xsL ysL : ImportedSumSequence.List T) :
  SsListRel xsR xsL -> SsListRel ysR ysL ->
  SsBoolRel (subseq xsR ysR) (ss_target_subseqb T xsL ysL).
Proof.
  intros Hxs Hys. unfold SsListRel in Hxs, Hys. unfold SsBoolRel.
  exact (sub_imported_eq_trans _ _ _
    (ss_subseqb_canonical T ysR xsR)
    (sub_imported_eq_congr2 (ss_target_subseqb T) _ _ _ _ Hxs Hys)).
Qed.

(** Reusable proposition-level combinators for the sequence-sum theorem
    cluster.  They compose the operation certificates above; no source or
    target theorem constant occurs in these proofs. *)

Lemma ss_imp_correspondence (P R : Prop) (Q S : SProp) :
  PropSPropRel P Q -> PropSPropRel R S ->
  PropSPropRel (P -> R) (Q -> S).
Proof.
  intros HP HR. apply prop_sprop_rel_intro.
  - intros H HQ. apply (prop_to_sprop _ _ HR).
    apply H. exact (sprop_to_prop _ _ HP HQ).
  - intro H. apply strictly_inhabits. intro HP0.
    apply (sprop_to_prop _ _ HR).
    apply H. exact (prop_to_sprop _ _ HP HP0).
Qed.

Lemma ss_forall_identity_correspondence (T : Type)
    (P : T -> Prop) (Q : T -> SProp) :
  (forall x, PropSPropRel (P x) (Q x)) ->
  PropSPropRel (forall x, P x) (forall x, Q x).
Proof.
  intro Hrel. apply prop_sprop_rel_intro.
  - intros H x. exact (prop_to_sprop _ _ (Hrel x) (H x)).
  - intro H. apply strictly_inhabits. intro x.
    exact (sprop_to_prop _ _ (Hrel x) (H x)).
Qed.

Lemma ss_pointwise_le_correspondence (T : eqType)
    (rR : seq T) (rL : ImportedSumSequence.List T)
    (PR : T -> bool) (PL : T -> ImportedSumSequence.Bool)
    (E1R E2R : T -> nat) (E1L E2L : T -> Lean.Nat) :
  SsListRel rR rL -> SsPredRel PR PL ->
  SsNatFunRel E1R E1L -> SsNatFunRel E2R E2L ->
  PropSPropRel
    (forall i, i \in rR -> PR i -> is_true (leq (E1R i) (E2R i)))
    (forall i, ss_target_mem i rL ->
      Lean.eq (PL i) ImportedSumSequence.Bool_true ->
      ss_target_le (E1L i) (E2L i)).
Proof.
  intros Hr HP HE1 HE2. apply prop_sprop_rel_intro.
  - intros H i Hmem HPi.
    apply (prop_to_sprop _ _
      (ss_le_correspondence (E1R i) (E1L i)
        (E2R i) (E2L i) (HE1 i) (HE2 i))).
    apply H.
    + exact (sprop_to_prop _ _
        (ss_membership_correspondence T i rR rL Hr) Hmem).
    + exact (sprop_to_prop _ _
        (ss_bool_true_correspondence (PR i) (PL i) (HP i)) HPi).
  - intro H. apply strictly_inhabits. intros i Hmem HPi.
    apply (sprop_to_prop _ _
      (ss_le_correspondence (E1R i) (E1L i)
        (E2R i) (E2L i) (HE1 i) (HE2 i))).
    apply H.
    + exact (prop_to_sprop _ _
        (ss_membership_correspondence T i rR rL Hr) Hmem).
    + exact (prop_to_sprop _ _
        (ss_bool_true_correspondence (PR i) (PL i) (HP i)) HPi).
Qed.

Lemma ss_pointwise_pred_imp_correspondence (T : eqType)
    (rR : seq T) (rL : ImportedSumSequence.List T)
    (P1R P2R : T -> bool)
    (P1L P2L : T -> ImportedSumSequence.Bool) :
  SsListRel rR rL -> SsPredRel P1R P1L -> SsPredRel P2R P2L ->
  PropSPropRel
    (forall i, i \in rR -> P1R i -> P2R i)
    (forall i, ss_target_mem i rL ->
      Lean.eq (P1L i) ImportedSumSequence.Bool_true ->
      Lean.eq (P2L i) ImportedSumSequence.Bool_true).
Proof.
  intros Hr HP1 HP2. apply prop_sprop_rel_intro.
  - intros H i Hmem HP1i.
    apply (prop_to_sprop _ _
      (ss_bool_true_correspondence (P2R i) (P2L i) (HP2 i))).
    apply H.
    + exact (sprop_to_prop _ _
        (ss_membership_correspondence T i rR rL Hr) Hmem).
    + exact (sprop_to_prop _ _
        (ss_bool_true_correspondence (P1R i) (P1L i) (HP1 i)) HP1i).
  - intro H. apply strictly_inhabits. intros i Hmem HP1i.
    apply (sprop_to_prop _ _
      (ss_bool_true_correspondence (P2R i) (P2L i) (HP2 i))).
    apply H.
    + exact (prop_to_sprop _ _
        (ss_membership_correspondence T i rR rL Hr) Hmem).
    + exact (prop_to_sprop _ _
        (ss_bool_true_correspondence (P1R i) (P1L i) (HP1 i)) HP1i).
Qed.

Lemma ss_pointwise_bool_split_correspondence (T : Type)
    (PR QR RR : T -> bool)
    (PL QL RL : T -> ImportedSumSequence.Bool) :
  SsPredRel PR PL -> SsPredRel QR QL -> SsPredRel RR RL ->
  PropSPropRel
    (forall x, Logic.eq (PR x) (QR x || RR x))
    (forall x, Lean.eq (PL x)
      (ImportedSumSequence.Bool_or (QL x) (RL x))).
Proof.
  intros HP HQ HR. apply prop_sprop_rel_intro.
  - intros H x. apply (prop_to_sprop _ _
      (ss_bool_eq_correspondence _ _ _ _ (HP x)
        (ss_bool_or_related _ _ _ _ (HQ x) (HR x)))).
    exact (H x).
  - intro H. apply strictly_inhabits. intro x.
    apply (sprop_to_prop _ _
      (ss_bool_eq_correspondence _ _ _ _ (HP x)
        (ss_bool_or_related _ _ _ _ (HQ x) (HR x)))).
    exact (H x).
Qed.

Lemma ss_pointwise_bool_exclusive_correspondence (T : Type)
    (QR RR : T -> bool)
    (QL RL : T -> ImportedSumSequence.Bool) :
  SsPredRel QR QL -> SsPredRel RR RL ->
  PropSPropRel
    (forall x, ~~ (QR x && RR x))
    (forall x,
      Lean.eq
        (ImportedSumSequence.Bool_not
          (ss_target_decide_bool_true
            (ImportedSumSequence.Bool_and (QL x) (RL x))))
        ImportedSumSequence.Bool_true).
Proof.
  intros HQ HR. apply prop_sprop_rel_intro.
  - intros H x.
    have Hand := ss_bool_and_related _ _ _ _ (HQ x) (HR x).
    have Hdec := ss_decide_bool_true_related _ _ Hand.
    have Hnot := ss_bool_not_related _ _ Hdec.
    exact (prop_to_sprop _ _ (ss_bool_true_correspondence _ _ Hnot) (H x)).
  - intro H. apply strictly_inhabits. intro x.
    have Hand := ss_bool_and_related _ _ _ _ (HQ x) (HR x).
    have Hdec := ss_decide_bool_true_related _ _ Hand.
    have Hnot := ss_bool_not_related _ _ Hdec.
    exact (sprop_to_prop _ _ (ss_bool_true_correspondence _ _ Hnot) (H x)).
Qed.

Lemma ss_pointwise_nat_eq_bool_correspondence (T : eqType)
    (rR : seq T) (rL : ImportedSumSequence.List T)
    (PR : T -> bool) (PL : T -> ImportedSumSequence.Bool)
    (E1R E2R : T -> nat) (E1L E2L : T -> Lean.Nat) :
  SsListRel rR rL -> SsPredRel PR PL ->
  SsNatFunRel E1R E1L -> SsNatFunRel E2R E2L ->
  PropSPropRel
    (forall i, i \in rR -> PR i -> E1R i == E2R i)
    (forall i, ss_target_mem i rL ->
      Lean.eq (PL i) ImportedSumSequence.Bool_true ->
      Lean.eq (ss_target_decide_nat_eq (E1L i) (E2L i))
        ImportedSumSequence.Bool_true).
Proof.
  intros Hr HP HE1 HE2. apply prop_sprop_rel_intro.
  - intros H i Hmem HPi.
    apply (prop_to_sprop _ _
      (ss_bool_true_correspondence
        (E1R i == E2R i)
        (ss_target_decide_nat_eq (E1L i) (E2L i))
        (ss_decide_nat_eq_related (E1R i) (E1L i)
          (E2R i) (E2L i) (HE1 i) (HE2 i)))).
    apply H.
    + exact (sprop_to_prop _ _
        (ss_membership_correspondence T i rR rL Hr) Hmem).
    + exact (sprop_to_prop _ _
        (ss_bool_true_correspondence (PR i) (PL i) (HP i)) HPi).
  - intro H. apply strictly_inhabits. intros i Hmem HPi.
    apply (sprop_to_prop _ _
      (ss_bool_true_correspondence
        (E1R i == E2R i)
        (ss_target_decide_nat_eq (E1L i) (E2L i))
        (ss_decide_nat_eq_related (E1R i) (E1L i)
          (E2R i) (E2L i) (HE1 i) (HE2 i)))).
    apply H.
    + exact (prop_to_sprop _ _
        (ss_membership_correspondence T i rR rL Hr) Hmem).
    + exact (prop_to_sprop _ _
        (ss_bool_true_correspondence (PR i) (PL i) (HP i)) HPi).
Qed.

Lemma ss_subset_correspondence (T : eqType)
    (rR rsR : seq T)
    (rL rsL : ImportedSumSequence.List T) :
  SsListRel rR rL -> SsListRel rsR rsL ->
  PropSPropRel
    (forall x, x \in rR -> x \in rsR)
    (forall x, ss_target_mem x rL -> ss_target_mem x rsL).
Proof.
  intros Hr Hrs. apply prop_sprop_rel_intro.
  - intros H x Hmem.
    apply (prop_to_sprop _ _
      (ss_membership_correspondence T x rsR rsL Hrs)).
    apply H. exact (sprop_to_prop _ _
      (ss_membership_correspondence T x rR rL Hr) Hmem).
  - intro H. apply strictly_inhabits. intros x Hmem.
    apply (sprop_to_prop _ _
      (ss_membership_correspondence T x rsR rsL Hrs)).
    apply H. exact (prop_to_sprop _ _
      (ss_membership_correspondence T x rR rL Hr) Hmem).
Qed.

(** Namespace-local [uniq]/[List.Nodup] correspondence. *)
Definition ss_nodup_transport {T : Type}
    (xs ys : ImportedSumSequence.List T) :
    Lean.eq xs ys -> ImportedSumSequence.List_Nodup T xs ->
    ImportedSumSequence.List_Nodup T ys :=
  fun Hxy H =>
    match Hxy in Lean.eq _ zs return ImportedSumSequence.List_Nodup T zs with
    | Lean.eq_refl => H
    end.

Definition ss_and_left_truth (a b : bool) :
    SsBoolTruth (a && b) -> SsBoolTruth a :=
  match a, b return SsBoolTruth (a && b) -> SsBoolTruth a with
  | true, _ => fun _ => ss_truth_intro
  | false, _ => fun H => H
  end.

Definition ss_and_right_truth (a b : bool) :
    SsBoolTruth (a && b) -> SsBoolTruth b :=
  match a, b return SsBoolTruth (a && b) -> SsBoolTruth b with
  | true, true => fun _ => ss_truth_intro
  | true, false => fun H => H
  | false, true => fun _ => ss_truth_intro
  | false, false => fun H => H
  end.

Definition ss_neg_mem_contra (b : bool) :
    SsBoolTruth (~~ b) -> SsBoolTruth b -> ImportedSumSequence.False :=
  match b return SsBoolTruth (~~ b) -> SsBoolTruth b ->
      ImportedSumSequence.False with
  | true => fun H _ => match H with end
  | false => fun _ H => match H with end
  end.

Fixpoint ss_uniq_truth_forward (T : eqType) (xs : seq T) :
    SsBoolTruth (uniq xs) ->
    ImportedSumSequence.List_Nodup T (ss_to_imported xs).
Proof.
  destruct xs as [|x xs].
  - intro Hnil. exact (ImportedSumSequence.List_Pairwise_nil T
      (ImportedSumSequence.Ne T)).
  - intro Huniq. apply ImportedSumSequence.List_Pairwise_cons.
    + intros y Hy Hxy.
      have HyR := sprop_to_prop _ _
        (ss_membership_correspondence T y xs (ss_to_imported xs)
          (@Lean.eq_refl _ _)) Hy.
      have Hcoq : Logic.eq x y := imported_eq_to_coq_eq x y Hxy.
      subst y.
      exact (ss_neg_mem_contra (x \in xs)
        (ss_and_left_truth _ _ Huniq) (ss_prop_to_truth _ HyR)).
    + exact (ss_uniq_truth_forward T xs (ss_and_right_truth _ _ Huniq)).
Defined.

Definition ss_uniq_forward (T : eqType) (xs : seq T) :
    uniq xs -> ImportedSumSequence.List_Nodup T (ss_to_imported xs) :=
  fun H => ss_uniq_truth_forward T xs (ss_prop_to_truth _ H).

Definition ss_strict_uniq_transport (T : eqType) (xs ys : seq T) :
    Logic.eq xs ys -> StrictlyInhabited (uniq xs) ->
    StrictlyInhabited (uniq ys) :=
  fun H Huniq =>
    match H in Logic.eq _ zs return StrictlyInhabited (uniq zs) with
    | Logic.eq_refl => Huniq
    end.

Lemma ss_imported_nodup_backward (T : eqType)
    (xs : ImportedSumSequence.List T) :
  ImportedSumSequence.List_Nodup T xs ->
  StrictlyInhabited (uniq (ss_to_rocq xs)).
Proof.
  intro Hnodup. induction Hnodup as [|y ys Hhead Htail IH].
  - exact (strictly_inhabits (Logic.eq_refl true)).
  - destruct IH as [IHuniq]. apply strictly_inhabits.
    apply/andP. split; last exact IHuniq.
    apply/negP. intro Hmem.
    have HmemL := prop_to_sprop _ _
      (ss_membership_correspondence T y (ss_to_rocq ys) ys
        (ss_list_target_roundtrip ys)) Hmem.
    have Hneq := Hhead y HmemL.
    exact (interpret_strict Logic.False
      (ss_false_to_strict (Hneq (@Lean.eq_refl T y)))).
Qed.

Lemma ss_uniq_backward (T : eqType) (xs : seq T) :
  ImportedSumSequence.List_Nodup T (ss_to_imported xs) ->
  StrictlyInhabited (uniq xs).
Proof.
  intro Hnodup.
  exact (ss_strict_uniq_transport T _ _ (ss_list_source_roundtrip xs)
    (ss_imported_nodup_backward T (ss_to_imported xs) Hnodup)).
Qed.

Lemma ss_uniq_correspondence (T : eqType)
    (xsR : seq T) (xsL : ImportedSumSequence.List T) :
  SsListRel xsR xsL ->
  PropSPropRel (uniq xsR) (ImportedSumSequence.List_Nodup T xsL).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intro Huniq. exact (ss_nodup_transport _ _ Hxs
      (ss_uniq_forward T xsR Huniq)).
  - intro Hnodup.
    have Hcanonical := ss_nodup_transport _ _
      (sub_imported_eq_sym _ _ Hxs) Hnodup.
    exact (ss_uniq_backward T xsR Hcanonical).
Qed.

Lemma ss_subseq_truth_correspondence (T : eqType)
    (r1R r2R : seq T)
    (r1L r2L : ImportedSumSequence.List T) :
  SsListRel r1R r1L -> SsListRel r2R r2L ->
  PropSPropRel (subseq r1R r2R)
    (Lean.eq (ss_target_subseqb T r1L r2L)
      ImportedSumSequence.Bool_true).
Proof.
  intros Hr1 Hr2.
  exact (ss_bool_true_correspondence _ _
    (ss_subseqb_related T r1R r2R r1L r2L Hr1 Hr2)).
Qed.

Lemma ss_sum_le_subseq_instance_correspondence (T : eqType)
    (PR : T -> bool) (PL : T -> ImportedSumSequence.Bool)
    (FR : T -> nat) (FL : T -> Lean.Nat)
    (r1R r2R : seq T)
    (r1L r2L : ImportedSumSequence.List T) :
  SsPredRel PR PL -> SsNatFunRel FR FL ->
  SsListRel r1R r1L -> SsListRel r2R r2L ->
  PropSPropRel
    (subseq r1R r2R ->
      is_true (leq (\sum_(x <- r1R | PR x) FR x)
        (\sum_(x <- r2R | PR x) FR x)))
    (Lean.eq (ss_target_subseqb T r1L r2L)
        ImportedSumSequence.Bool_true ->
      ss_target_le (ss_target_sumFiltered r1L PL FL)
        (ss_target_sumFiltered r2L PL FL)).
Proof.
  intros HP HF Hr1 Hr2. apply ss_imp_correspondence.
  - exact (ss_subseq_truth_correspondence T r1R r2R r1L r2L Hr1 Hr2).
  - apply ss_le_correspondence;
      apply ss_sumFiltered_related; assumption.
Qed.

Lemma ss_leq_sum_sub_uniq_instance_correspondence (T : eqType)
    (rR rsR : seq T)
    (rL rsL : ImportedSumSequence.List T)
    (FR : T -> nat) (FL : T -> Lean.Nat) :
  SsListRel rR rL -> SsListRel rsR rsL -> SsNatFunRel FR FL ->
  PropSPropRel
    (uniq rR -> (forall x, x \in rR -> x \in rsR) ->
      is_true (leq (\sum_(x <- rR) FR x) (\sum_(x <- rsR) FR x)))
    (ImportedSumSequence.List_Nodup T rL ->
      (forall x, ss_target_mem x rL -> ss_target_mem x rsL) ->
      ss_target_le (ss_target_sumSeq rL FL) (ss_target_sumSeq rsL FL)).
Proof.
  intros Hr Hrs HF. apply ss_imp_correspondence.
  - exact (ss_uniq_correspondence T rR rL Hr).
  - apply ss_imp_correspondence.
    + exact (ss_subset_correspondence T rR rsR rL rsL Hr Hrs).
    + apply ss_le_correspondence;
        apply ss_sumSeq_related; assumption.
Qed.

Lemma ss_filtered_sum_le_correspondence (T : Type)
    (PR : T -> bool) (PL : T -> ImportedSumSequence.Bool)
    (E1R E2R : T -> nat) (E1L E2L : T -> Lean.Nat)
    (rR : seq T) (rL : ImportedSumSequence.List T) :
  SsPredRel PR PL -> SsNatFunRel E1R E1L -> SsNatFunRel E2R E2L ->
  SsListRel rR rL ->
  PropSPropRel
    (is_true (leq (\sum_(i <- rR | PR i) E1R i)
      (\sum_(i <- rR | PR i) E2R i)))
    (ss_target_le (ss_target_sumFiltered rL PL E1L)
      (ss_target_sumFiltered rL PL E2L)).
Proof.
  intros HP HE1 HE2 Hr.
  apply ss_le_correspondence;
    apply ss_sumFiltered_related; assumption.
Qed.

Lemma ss_sumFiltered_le_correspondence (T : Type)
    (P1R P2R : T -> bool)
    (P1L P2L : T -> ImportedSumSequence.Bool)
    (ER : T -> nat) (EL : T -> Lean.Nat)
    (rR : seq T) (rL : ImportedSumSequence.List T) :
  SsPredRel P1R P1L -> SsPredRel P2R P2L -> SsNatFunRel ER EL ->
  SsListRel rR rL ->
  PropSPropRel
    (is_true (leq (\sum_(i <- rR | P1R i) ER i)
      (\sum_(i <- rR | P2R i) ER i)))
    (ss_target_le (ss_target_sumFiltered rL P1L EL)
      (ss_target_sumFiltered rL P2L EL)).
Proof.
  intros HP1 HP2 HE Hr.
  apply ss_le_correspondence;
    apply ss_sumFiltered_related; assumption.
Qed.

Lemma ss_filtered_sum_eq_correspondence (T : Type)
    (PR : T -> bool) (PL : T -> ImportedSumSequence.Bool)
    (E1R E2R : T -> nat) (E1L E2L : T -> Lean.Nat)
    (rR : seq T) (rL : ImportedSumSequence.List T) :
  SsPredRel PR PL -> SsNatFunRel E1R E1L -> SsNatFunRel E2R E2L ->
  SsListRel rR rL ->
  PropSPropRel
    (Logic.eq (\sum_(i <- rR | PR i) E1R i)
      (\sum_(i <- rR | PR i) E2R i))
    (Lean.eq (ss_target_sumFiltered rL PL E1L)
      (ss_target_sumFiltered rL PL E2L)).
Proof.
  intros HP HE1 HE2 Hr.
  apply sub_nat_eq_correspondence;
    apply ss_sumFiltered_related; assumption.
Qed.

Lemma ss_leq_sum_seq_instance_correspondence (T : eqType)
    (rR : seq T) (rL : ImportedSumSequence.List T)
    (PR : T -> bool) (PL : T -> ImportedSumSequence.Bool)
    (E1R E2R : T -> nat) (E1L E2L : T -> Lean.Nat) :
  SsListRel rR rL -> SsPredRel PR PL ->
  SsNatFunRel E1R E1L -> SsNatFunRel E2R E2L ->
  PropSPropRel
    ((forall i, i \in rR -> PR i -> is_true (leq (E1R i) (E2R i))) ->
      is_true (leq (\sum_(i <- rR | PR i) E1R i)
        (\sum_(i <- rR | PR i) E2R i)))
    ((forall i, ss_target_mem i rL ->
        Lean.eq (PL i) ImportedSumSequence.Bool_true ->
        ss_target_le (E1L i) (E2L i)) ->
      ss_target_le (ss_target_sumFiltered rL PL E1L)
        (ss_target_sumFiltered rL PL E2L)).
Proof.
  intros Hr HP HE1 HE2. apply ss_imp_correspondence.
  - exact (ss_pointwise_le_correspondence T rR rL PR PL
      E1R E2R E1L E2L Hr HP HE1 HE2).
  - exact (ss_filtered_sum_le_correspondence T PR PL
      E1R E2R E1L E2L rR rL HP HE1 HE2 Hr).
Qed.

Lemma ss_eq_sum_seq_instance_correspondence (T : eqType)
    (rR : seq T) (rL : ImportedSumSequence.List T)
    (PR : T -> bool) (PL : T -> ImportedSumSequence.Bool)
    (E1R E2R : T -> nat) (E1L E2L : T -> Lean.Nat) :
  SsListRel rR rL -> SsPredRel PR PL ->
  SsNatFunRel E1R E1L -> SsNatFunRel E2R E2L ->
  PropSPropRel
    ((forall i, i \in rR -> PR i -> E1R i == E2R i) ->
      Logic.eq (\sum_(i <- rR | PR i) E1R i)
        (\sum_(i <- rR | PR i) E2R i))
    ((forall i, ss_target_mem i rL ->
        Lean.eq (PL i) ImportedSumSequence.Bool_true ->
        Lean.eq (ss_target_decide_nat_eq (E1L i) (E2L i))
          ImportedSumSequence.Bool_true) ->
      Lean.eq (ss_target_sumFiltered rL PL E1L)
        (ss_target_sumFiltered rL PL E2L)).
Proof.
  intros Hr HP HE1 HE2. apply ss_imp_correspondence.
  - exact (ss_pointwise_nat_eq_bool_correspondence T rR rL PR PL
      E1R E2R E1L E2L Hr HP HE1 HE2).
  - exact (ss_filtered_sum_eq_correspondence T PR PL
      E1R E2R E1L E2L rR rL HP HE1 HE2 Hr).
Qed.

Lemma ss_leq_sum_seq_pred_instance_correspondence (T : eqType)
    (rR : seq T) (rL : ImportedSumSequence.List T)
    (ER : T -> nat) (EL : T -> Lean.Nat)
    (P1R P2R : T -> bool)
    (P1L P2L : T -> ImportedSumSequence.Bool) :
  SsListRel rR rL -> SsNatFunRel ER EL ->
  SsPredRel P1R P1L -> SsPredRel P2R P2L ->
  PropSPropRel
    ((forall i, i \in rR -> P1R i -> P2R i) ->
      is_true (leq (\sum_(i <- rR | P1R i) ER i)
        (\sum_(i <- rR | P2R i) ER i)))
    ((forall i, ss_target_mem i rL ->
        Lean.eq (P1L i) ImportedSumSequence.Bool_true ->
        Lean.eq (P2L i) ImportedSumSequence.Bool_true) ->
      ss_target_le (ss_target_sumFiltered rL P1L EL)
        (ss_target_sumFiltered rL P2L EL)).
Proof.
  intros Hr HE HP1 HP2. apply ss_imp_correspondence.
  - exact (ss_pointwise_pred_imp_correspondence T rR rL
      P1R P2R P1L P2L Hr HP1 HP2).
  - exact (ss_sumFiltered_le_correspondence T P1R P2R P1L P2L
      ER EL rR rL HP1 HP2 HE Hr).
Qed.

Lemma ss_ltn_sum_leq_seq_instance_correspondence (T : eqType)
    (rR : seq T) (rL : ImportedSumSequence.List T)
    (PR : T -> bool) (PL : T -> ImportedSumSequence.Bool)
    (E1R E2R : T -> nat) (E1L E2L : T -> Lean.Nat) (j : T) :
  SsListRel rR rL -> SsPredRel PR PL ->
  SsNatFunRel E1R E1L -> SsNatFunRel E2R E2L ->
  PropSPropRel
    (j \in rR -> PR j -> is_true (ltn (E1R j) (E2R j)) ->
      (forall i, i \in rR -> PR i -> is_true (leq (E1R i) (E2R i))) ->
      is_true (ltn (\sum_(x <- rR | PR x) E1R x)
        (\sum_(x <- rR | PR x) E2R x)))
    (ss_target_mem j rL ->
      Lean.eq (PL j) ImportedSumSequence.Bool_true ->
      ss_target_lt (E1L j) (E2L j) ->
      (forall i, ss_target_mem i rL ->
        Lean.eq (PL i) ImportedSumSequence.Bool_true ->
        ss_target_le (E1L i) (E2L i)) ->
      ss_target_lt (ss_target_sumFiltered rL PL E1L)
        (ss_target_sumFiltered rL PL E2L)).
Proof.
  intros Hr HP HE1 HE2.
  apply ss_imp_correspondence.
  - exact (ss_membership_correspondence T j rR rL Hr).
  - apply ss_imp_correspondence.
    + exact (ss_bool_true_correspondence (PR j) (PL j) (HP j)).
    + apply ss_imp_correspondence.
      * exact (ss_lt_correspondence (E1R j) (E1L j)
          (E2R j) (E2L j) (HE1 j) (HE2 j)).
      * apply ss_imp_correspondence.
        -- exact (ss_pointwise_le_correspondence T rR rL PR PL
             E1R E2R E1L E2L Hr HP HE1 HE2).
        -- apply ss_lt_correspondence;
             apply ss_sumFiltered_related; assumption.
Qed.

Lemma ss_eq_sum_leq_seq_instance_correspondence (T : eqType)
    (rR : seq T) (rL : ImportedSumSequence.List T)
    (PR : T -> bool) (PL : T -> ImportedSumSequence.Bool)
    (E1R E2R : T -> nat) (E1L E2L : T -> Lean.Nat) :
  SsListRel rR rL -> SsPredRel PR PL ->
  SsNatFunRel E1R E1L -> SsNatFunRel E2R E2L ->
  PropSPropRel
    ((forall i, i \in rR -> PR i -> is_true (leq (E1R i) (E2R i))) ->
      Logic.eq
        (\sum_(x <- rR | PR x) E1R x == \sum_(x <- rR | PR x) E2R x)
        (all (fun x => E1R x == E2R x) [seq x <- rR | PR x]))
    ((forall i, ss_target_mem i rL ->
        Lean.eq (PL i) ImportedSumSequence.Bool_true ->
        ss_target_le (E1L i) (E2L i)) ->
      Lean.eq
        (ss_target_decide_nat_eq
          (ss_target_sumFiltered rL PL E1L)
          (ss_target_sumFiltered rL PL E2L))
        (ss_target_all rL
          (fun x => ImportedSumSequence.Bool_or
            (ImportedSumSequence.Bool_not (PL x))
            (ss_target_decide_nat_eq (E1L x) (E2L x))))).
Proof.
  intros Hr HP HE1 HE2. apply ss_imp_correspondence.
  - exact (ss_pointwise_le_correspondence T rR rL PR PL
      E1R E2R E1L E2L Hr HP HE1 HE2).
  - have Hsum1 := ss_sumFiltered_related T PR PL E1R E1L
      rR rL HP HE1 Hr.
    have Hsum2 := ss_sumFiltered_related T PR PL E2R E2L
      rR rL HP HE2 Hr.
    have Hlhs := ss_decide_nat_eq_related
      (\sum_(x <- rR | PR x) E1R x)
      (ss_target_sumFiltered rL PL E1L)
      (\sum_(x <- rR | PR x) E2R x)
      (ss_target_sumFiltered rL PL E2L) Hsum1 Hsum2.
    have HQ : SsPredRel (fun x => E1R x == E2R x)
        (fun x => ss_target_decide_nat_eq (E1L x) (E2L x)) :=
      fun x => ss_decide_nat_eq_related (E1R x) (E1L x)
        (E2R x) (E2L x) (HE1 x) (HE2 x).
    have Hrhs := ss_all_filter_imp_related T PR
      (fun x => E1R x == E2R x) PL
      (fun x => ss_target_decide_nat_eq (E1L x) (E2L x))
      rR rL HP HQ Hr.
    exact (ss_bool_eq_correspondence _ _ _ _ Hlhs Hrhs).
Qed.

Lemma ss_sum_split_instance_correspondence (T : eqType)
    (rR : seq T) (rL : ImportedSumSequence.List T)
    (PR QR RR : T -> bool)
    (PL QL RL : T -> ImportedSumSequence.Bool)
    (FR : T -> nat) (FL : T -> Lean.Nat) :
  SsListRel rR rL ->
  SsPredRel PR PL -> SsPredRel QR QL -> SsPredRel RR RL ->
  SsNatFunRel FR FL ->
  PropSPropRel
    ((forall x, Logic.eq (PR x) (QR x || RR x)) ->
      (forall x, ~~ (QR x && RR x)) ->
      Logic.eq (\sum_(x <- rR | PR x) FR x)
        (\sum_(x <- rR | QR x) FR x + \sum_(x <- rR | RR x) FR x))
    ((forall x, Lean.eq (PL x)
        (ImportedSumSequence.Bool_or (QL x) (RL x))) ->
      (forall x,
        Lean.eq
          (ImportedSumSequence.Bool_not
            (ss_target_decide_bool_true
              (ImportedSumSequence.Bool_and (QL x) (RL x))))
          ImportedSumSequence.Bool_true) ->
      Lean.eq (ss_target_sumFiltered rL PL FL)
        (ss_target_add (ss_target_sumFiltered rL QL FL)
          (ss_target_sumFiltered rL RL FL))).
Proof.
  intros Hr HP HQ HR HF. apply ss_imp_correspondence.
  - exact (ss_pointwise_bool_split_correspondence T PR QR RR PL QL RL
      HP HQ HR).
  - apply ss_imp_correspondence.
    + exact (ss_pointwise_bool_exclusive_correspondence T QR RR QL RL
        HQ HR).
    + have HsumP := ss_sumFiltered_related T PR PL FR FL rR rL HP HF Hr.
      have HsumQ := ss_sumFiltered_related T QR QL FR FL rR rL HQ HF Hr.
      have HsumR := ss_sumFiltered_related T RR RL FR FL rR rL HR HF Hr.
      have Hadd := ss_add_related
        (\sum_(x <- rR | QR x) FR x) (ss_target_sumFiltered rL QL FL)
        (\sum_(x <- rR | RR x) FR x) (ss_target_sumFiltered rL RL FL)
        HsumQ HsumR.
      exact (sub_nat_eq_correspondence _ _ _ _ HsumP Hadd).
Qed.

(** Partitioned ordered-sequence sums. *)
Definition ss_target_sumOfPartition (X Y : eqType)
    (xToY : X -> Y) (f : X -> Lean.Nat)
    (P : X -> ImportedSumSequence.Bool)
    (xs : ImportedSumSequence.List X) (y : Y) : Lean.Nat :=
  ImportedSumSequence.Prosa_Util_Sum_sumOfPartition X Y
    (ss_decidable_eq Y) xToY f P xs y.

Definition ss_target_sumOverPartitions (X Y : eqType)
    (xToY : X -> Y) (f : X -> Lean.Nat)
    (P : X -> ImportedSumSequence.Bool)
    (xs : ImportedSumSequence.List X)
    (ys : ImportedSumSequence.List Y) : Lean.Nat :=
  ImportedSumSequence.Prosa_Util_Sum_sumOverPartitions X Y
    (ss_decidable_eq Y) xToY f P xs ys.

Lemma ss_sumOfPartition_related (X Y : eqType)
    (xToY : X -> Y)
    (fR : X -> nat) (fL : X -> Lean.Nat)
    (PR : X -> bool) (PL : X -> ImportedSumSequence.Bool)
    (xsR : seq X) (xsL : ImportedSumSequence.List X) (y : Y) :
  SsNatFunRel fR fL -> SsPredRel PR PL -> SsListRel xsR xsL ->
  SubNatRel
    (\sum_(x <- xsR | PR x && (xToY x == y)) fR x)
    (ss_target_sumOfPartition X Y xToY fL PL xsL y).
Proof.
  intros Hf HP Hxs.
  have Hpart : SsPredRel
      (fun x => PR x && (xToY x == y))
      (fun x => ImportedSumSequence.Bool_and (PL x)
        (ss_target_decide_eq Y (xToY x) y)) :=
    fun x => ss_bool_and_related _ _ _ _ (HP x)
      (ss_decide_eq_related Y (xToY x) y).
  have Hsum := ss_sumFiltered_related X
    (fun x => PR x && (xToY x == y))
    (fun x => ImportedSumSequence.Bool_and (PL x)
      (ss_target_decide_eq Y (xToY x) y))
    fR fL xsR xsL Hpart Hf Hxs.
  unfold SubNatRel in Hsum |- *.
  exact (sub_imported_eq_trans _ _ _ Hsum
    (sub_imported_eq_sym _ _
      (ImportedSumSequence.Prosa_Validation_SumSequenceInterface_production_sumOfPartition_eq
        X Y (ss_decidable_eq Y) xToY fL PL xsL y))).
Qed.

Lemma ss_sumOverPartitions_related (X Y : eqType)
    (xToY : X -> Y)
    (fR : X -> nat) (fL : X -> Lean.Nat)
    (PR : X -> bool) (PL : X -> ImportedSumSequence.Bool)
    (xsR : seq X) (xsL : ImportedSumSequence.List X)
    (ysR : seq Y) (ysL : ImportedSumSequence.List Y) :
  SsNatFunRel fR fL -> SsPredRel PR PL ->
  SsListRel xsR xsL -> SsListRel ysR ysL ->
  SubNatRel
    (\sum_(y <- ysR) \sum_(x <- xsR | PR x && (xToY x == y)) fR x)
    (ss_target_sumOverPartitions X Y xToY fL PL xsL ysL).
Proof.
  intros Hf HP Hxs Hys.
  have Hpart : SsNatFunRel
      (fun y => \sum_(x <- xsR | PR x && (xToY x == y)) fR x)
      (fun y => ss_target_sumOfPartition X Y xToY fL PL xsL y) :=
    fun y => ss_sumOfPartition_related X Y xToY fR fL PR PL
      xsR xsL y Hf HP Hxs.
  have Hsum := ss_sumSeq_related Y _ _ ysR ysL Hpart Hys.
  unfold SubNatRel in Hsum |- *.
  exact (sub_imported_eq_trans _ _ _ Hsum
    (sub_imported_eq_sym _ _
      (ImportedSumSequence.Prosa_Validation_SumSequenceInterface_production_sumOverPartitions_eq
        X Y (ss_decidable_eq Y) xToY fL PL xsL ysL))).
Qed.

Lemma ss_partition_covered_correspondence (X Y : eqType)
    (xToY : X -> Y)
    (PR : X -> bool) (PL : X -> ImportedSumSequence.Bool)
    (xsR : seq X) (xsL : ImportedSumSequence.List X)
    (ysR : seq Y) (ysL : ImportedSumSequence.List Y) :
  SsPredRel PR PL -> SsListRel xsR xsL -> SsListRel ysR ysL ->
  PropSPropRel
    (forall x, x \in xsR -> PR x -> xToY x \in ysR)
    (forall x, ss_target_mem x xsL ->
      Lean.eq (PL x) ImportedSumSequence.Bool_true ->
      ss_target_mem (xToY x) ysL).
Proof.
  intros HP Hxs Hys. apply prop_sprop_rel_intro.
  - intros H x Hx HPx.
    apply (prop_to_sprop _ _
      (ss_membership_correspondence Y (xToY x) ysR ysL Hys)).
    apply H.
    + exact (sprop_to_prop _ _
        (ss_membership_correspondence X x xsR xsL Hxs) Hx).
    + exact (sprop_to_prop _ _
        (ss_bool_true_correspondence (PR x) (PL x) (HP x)) HPx).
  - intro H. apply strictly_inhabits. intros x Hx HPx.
    apply (sprop_to_prop _ _
      (ss_membership_correspondence Y (xToY x) ysR ysL Hys)).
    apply H.
    + exact (prop_to_sprop _ _
        (ss_membership_correspondence X x xsR xsL Hxs) Hx).
    + exact (prop_to_sprop _ _
        (ss_bool_true_correspondence (PR x) (PL x) (HP x)) HPx).
Qed.

Lemma ss_sum_over_partitions_le_instance_correspondence (X Y : eqType)
    (xToY : X -> Y)
    (fR : X -> nat) (fL : X -> Lean.Nat)
    (PR : X -> bool) (PL : X -> ImportedSumSequence.Bool)
    (xsR : seq X) (xsL : ImportedSumSequence.List X)
    (ysR : seq Y) (ysL : ImportedSumSequence.List Y) :
  SsNatFunRel fR fL -> SsPredRel PR PL ->
  SsListRel xsR xsL -> SsListRel ysR ysL ->
  PropSPropRel
    ((forall x, x \in xsR -> PR x -> xToY x \in ysR) ->
      is_true (leq (\sum_(x <- xsR | PR x) fR x)
        (\sum_(y <- ysR)
          \sum_(x <- xsR | PR x && (xToY x == y)) fR x)))
    ((forall x, ss_target_mem x xsL ->
        Lean.eq (PL x) ImportedSumSequence.Bool_true ->
        ss_target_mem (xToY x) ysL) ->
      ss_target_le (ss_target_sumFiltered xsL PL fL)
        (ss_target_sumOverPartitions X Y xToY fL PL xsL ysL)).
Proof.
  intros Hf HP Hxs Hys. apply ss_imp_correspondence.
  - exact (ss_partition_covered_correspondence X Y xToY PR PL
      xsR xsL ysR ysL HP Hxs Hys).
  - apply ss_le_correspondence.
    + exact (ss_sumFiltered_related X PR PL fR fL xsR xsL HP Hf Hxs).
    + exact (ss_sumOverPartitions_related X Y xToY fR fL PR PL
        xsR xsL ysR ysL Hf HP Hxs Hys).
Qed.

Lemma ss_sum_over_partitions_eq_instance_correspondence (X Y : eqType)
    (xToY : X -> Y)
    (fR : X -> nat) (fL : X -> Lean.Nat)
    (PR : X -> bool) (PL : X -> ImportedSumSequence.Bool)
    (xsR : seq X) (xsL : ImportedSumSequence.List X)
    (ysR : seq Y) (ysL : ImportedSumSequence.List Y) :
  SsNatFunRel fR fL -> SsPredRel PR PL ->
  SsListRel xsR xsL -> SsListRel ysR ysL ->
  PropSPropRel
    ((forall x, x \in xsR -> PR x -> xToY x \in ysR) ->
      uniq xsR -> uniq ysR ->
      Logic.eq (\sum_(x <- xsR | PR x) fR x)
        (\sum_(y <- ysR)
          \sum_(x <- xsR | PR x && (xToY x == y)) fR x))
    ((forall x, ss_target_mem x xsL ->
        Lean.eq (PL x) ImportedSumSequence.Bool_true ->
        ss_target_mem (xToY x) ysL) ->
      ImportedSumSequence.List_Nodup X xsL ->
      ImportedSumSequence.List_Nodup Y ysL ->
      Lean.eq (ss_target_sumFiltered xsL PL fL)
        (ss_target_sumOverPartitions X Y xToY fL PL xsL ysL)).
Proof.
  intros Hf HP Hxs Hys. apply ss_imp_correspondence.
  - exact (ss_partition_covered_correspondence X Y xToY PR PL
      xsR xsL ysR ysL HP Hxs Hys).
  - apply ss_imp_correspondence.
    + exact (ss_uniq_correspondence X xsR xsL Hxs).
    + apply ss_imp_correspondence.
      * exact (ss_uniq_correspondence Y ysR ysL Hys).
      * apply sub_nat_eq_correspondence.
        -- exact (ss_sumFiltered_related X PR PL fR fL
             xsR xsL HP Hf Hxs).
        -- exact (ss_sumOverPartitions_related X Y xToY fR fL PR PL
             xsR xsL ysR ysL Hf HP Hxs Hys).
Qed.

Lemma ss_reorder_summation_result_correspondence (X Y : eqType)
    (xToY : X -> Y)
    (fR : X -> nat) (fL : X -> Lean.Nat)
    (PR : X -> bool) (PL : X -> ImportedSumSequence.Bool)
    (xsR : seq X) (xsL : ImportedSumSequence.List X)
    (ysR : seq Y) (ysL : ImportedSumSequence.List Y) (y' : Y) :
  SsNatFunRel fR fL -> SsPredRel PR PL ->
  SsListRel xsR xsL -> SsListRel ysR ysL ->
  PropSPropRel
    (is_true (leq
      (\sum_(x <- xsR | PR x && (xToY x != y')) fR x)
      (\sum_(y <- ysR | y != y')
        \sum_(x <- xsR | PR x && (xToY x == y)) fR x)))
    (ss_target_le
      (ss_target_sumFiltered xsL
        (fun x => ImportedSumSequence.Bool_and (PL x)
          (ss_target_decide_ne Y (xToY x) y')) fL)
      (ss_target_sumOverPartitions X Y xToY fL PL xsL
        (ss_target_filter (fun y => ss_target_decide_ne Y y y') ysL))).
Proof.
  intros Hf HP Hxs Hys.
  have HneqX : SsPredRel (fun x => xToY x != y')
      (fun x => ss_target_decide_ne Y (xToY x) y') :=
    fun x => ss_decide_ne_related Y (xToY x) y'.
  have HleftPred : SsPredRel (fun x => PR x && (xToY x != y'))
      (fun x => ImportedSumSequence.Bool_and (PL x)
        (ss_target_decide_ne Y (xToY x) y')) :=
    fun x => ss_bool_and_related _ _ _ _ (HP x) (HneqX x).
  have Hleft := ss_sumFiltered_related X _ _ fR fL xsR xsL
    HleftPred Hf Hxs.
  have HneqY : SsPredRel (fun y : Y => y != y')
      (fun y => ss_target_decide_ne Y y y') :=
    fun y => ss_decide_ne_related Y y y'.
  have HysFilter := ss_filter_related Y (fun y => y != y')
    (fun y => ss_target_decide_ne Y y y') ysR ysL HneqY Hys.
  have Hright0 := ss_sumOverPartitions_related X Y xToY fR fL PR PL
    xsR xsL [seq y <- ysR | y != y']
    (ss_target_filter (fun y => ss_target_decide_ne Y y y') ysL)
    Hf HP Hxs HysFilter.
  apply ss_le_correspondence.
  - exact Hleft.
  - unfold SubNatRel in Hright0 |- *.
    rewrite (ss_filtered_bigop_as_filter Y (fun y => y != y')
      (fun y => \sum_(x <- xsR | PR x && (xToY x == y)) fR x) ysR).
    exact Hright0.
Qed.

Lemma ss_reorder_summation_instance_correspondence (X Y : eqType)
    (xToY : X -> Y)
    (fR : X -> nat) (fL : X -> Lean.Nat)
    (PR : X -> bool) (PL : X -> ImportedSumSequence.Bool)
    (xsR : seq X) (xsL : ImportedSumSequence.List X)
    (ysR : seq Y) (ysL : ImportedSumSequence.List Y) :
  SsNatFunRel fR fL -> SsPredRel PR PL ->
  SsListRel xsR xsL -> SsListRel ysR ysL ->
  PropSPropRel
    ((forall x, x \in xsR -> PR x -> xToY x \in ysR) ->
      forall y', is_true (leq
        (\sum_(x <- xsR | PR x && (xToY x != y')) fR x)
        (\sum_(y <- ysR | y != y')
          \sum_(x <- xsR | PR x && (xToY x == y)) fR x)))
    ((forall x, ss_target_mem x xsL ->
        Lean.eq (PL x) ImportedSumSequence.Bool_true ->
        ss_target_mem (xToY x) ysL) ->
      forall y', ss_target_le
        (ss_target_sumFiltered xsL
          (fun x => ImportedSumSequence.Bool_and (PL x)
            (ss_target_decide_ne Y (xToY x) y')) fL)
        (ss_target_sumOverPartitions X Y xToY fL PL xsL
          (ss_target_filter (fun y => ss_target_decide_ne Y y y') ysL))).
Proof.
  intros Hf HP Hxs Hys. apply ss_imp_correspondence.
  - exact (ss_partition_covered_correspondence X Y xToY PR PL
      xsR xsL ysR ysL HP Hxs Hys).
  - apply ss_forall_identity_correspondence. intro y'.
    exact (ss_reorder_summation_result_correspondence X Y xToY
      fR fL PR PL xsR xsL ysR ysL y' Hf HP Hxs Hys).
Qed.

(** Higher-order Nat-function correspondence used by [sum_leq_mono]. *)
Definition ss_nat_endofun_to_imported (f : nat -> nat) :
    Lean.Nat -> Lean.Nat :=
  fun x => sub_nat_to_imported (f (sub_nat_to_rocq x)).

Definition ss_nat_endofun_to_rocq (f : Lean.Nat -> Lean.Nat) :
    nat -> nat :=
  fun x => sub_nat_to_rocq (f (sub_nat_to_imported x)).

Lemma ss_nat_endofun_canonical (f : nat -> nat) :
  SubNatFunRel f (ss_nat_endofun_to_imported f).
Proof.
  intros xR xL Hx. unfold SubNatRel in Hx |- *.
  destruct Hx. unfold ss_nat_endofun_to_imported.
  rewrite (sub_nat_rocq_roundtrip xR).
  exact (@Lean.eq_refl _ _).
Qed.

Lemma ss_nat_endofun_surjective (f : Lean.Nat -> Lean.Nat) :
  SubNatFunRel (ss_nat_endofun_to_rocq f) f.
Proof.
  intros xR xL Hx. unfold SubNatRel in Hx |- *.
  destruct Hx. unfold ss_nat_endofun_to_rocq.
  exact (sub_nat_imported_roundtrip (f (sub_nat_to_imported xR))).
Qed.

Definition SsNatFamilyRel {I : Type}
    (FR : I -> nat -> nat) (FL : I -> Lean.Nat -> Lean.Nat) : SProp :=
  forall i, SubNatFunRel (FR i) (FL i).

Definition ss_nat_family_to_imported {I : Type}
    (F : I -> nat -> nat) : I -> Lean.Nat -> Lean.Nat :=
  fun i => ss_nat_endofun_to_imported (F i).

Definition ss_nat_family_to_rocq {I : Type}
    (F : I -> Lean.Nat -> Lean.Nat) : I -> nat -> nat :=
  fun i => ss_nat_endofun_to_rocq (F i).

Lemma ss_nat_family_canonical {I : Type} (F : I -> nat -> nat) :
  SsNatFamilyRel F (ss_nat_family_to_imported F).
Proof. intro i. exact (ss_nat_endofun_canonical (F i)). Qed.

Lemma ss_nat_family_surjective {I : Type}
    (F : I -> Lean.Nat -> Lean.Nat) :
  SsNatFamilyRel (ss_nat_family_to_rocq F) F.
Proof. intro i. exact (ss_nat_endofun_surjective (F i)). Qed.

Definition ss_target_monotone (f : Lean.Nat -> Lean.Nat) : SProp :=
  ImportedSumSequence.Prosa_Util_Rel_monotone_inst1 Lean.Nat
    ss_target_decide_le f.

Lemma ss_monotone_correspondence
    (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat) :
  SubNatFunRel fR fL ->
  PropSPropRel
    (forall x y, is_true (leq x y) ->
      is_true (leq (fR x) (fR y)))
    (ss_target_monotone fL).
Proof.
  intro Hf. apply prop_sprop_rel_intro.
  - intros HR xL yL HxyL.
    pose xR := sub_nat_to_rocq xL.
    pose yR := sub_nat_to_rocq yL.
    have Hx : SubNatRel xR xL := sub_nat_rel_surjective xL.
    have Hy : SubNatRel yR yL := sub_nat_rel_surjective yL.
    have HxyR := sprop_to_prop _ _
      (ss_decide_le_true_correspondence _ _ _ _ Hx Hy) HxyL.
    exact (prop_to_sprop _ _
      (ss_decide_le_true_correspondence _ _ _ _
        (Hf _ _ Hx) (Hf _ _ Hy))
      (HR xR yR HxyR)).
  - intro HL. apply strictly_inhabits. intros xR yR HxyR.
    have Hx : SubNatRel xR (sub_nat_to_imported xR) :=
      sub_nat_rel_canonical xR.
    have Hy : SubNatRel yR (sub_nat_to_imported yR) :=
      sub_nat_rel_canonical yR.
    have HxyL := prop_to_sprop _ _
      (ss_decide_le_true_correspondence _ _ _ _ Hx Hy) HxyR.
    exact (sprop_to_prop _ _
      (ss_decide_le_true_correspondence _ _ _ _
        (Hf _ _ Hx) (Hf _ _ Hy))
      (HL _ _ HxyL)).
Qed.

Lemma ss_pointwise_monotone_correspondence (I : eqType)
    (rR : seq I) (rL : ImportedSumSequence.List I)
    (FR : I -> nat -> nat) (FL : I -> Lean.Nat -> Lean.Nat) :
  SsListRel rR rL -> SsNatFamilyRel FR FL ->
  PropSPropRel
    (forall i, i \in rR ->
      forall x y, is_true (leq x y) ->
        is_true (leq (FR i x) (FR i y)))
    (forall i, ss_target_mem i rL -> ss_target_monotone (FL i)).
Proof.
  intros Hr HF. apply prop_sprop_rel_intro.
  - intros HR i HmemL. apply (prop_to_sprop _ _
      (ss_monotone_correspondence (FR i) (FL i) (HF i))).
    apply HR. exact (sprop_to_prop _ _
      (ss_membership_correspondence I i rR rL Hr) HmemL).
  - intro HL. apply strictly_inhabits. intros i HmemR.
    apply (sprop_to_prop _ _
      (ss_monotone_correspondence (FR i) (FL i) (HF i))).
    apply HL. exact (prop_to_sprop _ _
      (ss_membership_correspondence I i rR rL Hr) HmemR).
Qed.

Lemma ss_filtered_family_sum_related (I : eqType)
    (PR : I -> bool) (PL : I -> ImportedSumSequence.Bool)
    (FR : I -> nat -> nat) (FL : I -> Lean.Nat -> Lean.Nat)
    (rR : seq I) (rL : ImportedSumSequence.List I) :
  SsPredRel PR PL -> SsNatFamilyRel FR FL -> SsListRel rR rL ->
  SubNatFunRel
    (fun x => \sum_(i <- rR | PR i) FR i x)
    (fun x => ss_target_sumFiltered rL PL (fun i => FL i x)).
Proof.
  intros HP HF Hr xR xL Hx.
  apply ss_sumFiltered_related.
  - exact HP.
  - intro i. exact (HF i _ _ Hx).
  - exact Hr.
Qed.

Lemma ss_sum_leq_mono_instance_correspondence (I : eqType)
    (PR : I -> bool) (PL : I -> ImportedSumSequence.Bool)
    (FR : I -> nat -> nat) (FL : I -> Lean.Nat -> Lean.Nat)
    (rR : seq I) (rL : ImportedSumSequence.List I) :
  SsPredRel PR PL -> SsNatFamilyRel FR FL -> SsListRel rR rL ->
  PropSPropRel
    ((forall i, i \in rR ->
       forall x y, is_true (leq x y) ->
         is_true (leq (FR i x) (FR i y))) ->
      forall x y, is_true (leq x y) ->
        is_true (leq
          (\sum_(i <- rR | PR i) FR i x)
          (\sum_(i <- rR | PR i) FR i y)))
    ((forall i, ss_target_mem i rL -> ss_target_monotone (FL i)) ->
      ss_target_monotone
        (fun x => ss_target_sumFiltered rL PL (fun i => FL i x))).
Proof.
  intros HP HF Hr. apply ss_imp_correspondence.
  - exact (ss_pointwise_monotone_correspondence I rR rL FR FL Hr HF).
  - apply ss_monotone_correspondence.
    exact (ss_filtered_family_sum_related I PR PL FR FL rR rL HP HF Hr).
Qed.

(** The one-element finite enumeration used by [sum_unit1].  The target
    value below is the exact imported [Finset.univ] sum expression, not a
    hand-written replacement. *)
Definition ss_target_unit_sum
    (F : ImportedSumSequence.Unit -> Lean.Nat) : Lean.Nat :=
  ImportedSumSequence.Finset_sum_inst3 ImportedSumSequence.Unit Lean.Nat
    ImportedSumSequence.Nat_instAddCommMonoid
    (ImportedSumSequence.Finset_univ_inst1 ImportedSumSequence.Unit
      ImportedSumSequence.PUnit_fintype_inst1) F.

Definition SsUnitNatFunRel (FR : unit -> nat)
    (FL : ImportedSumSequence.Unit -> Lean.Nat) : SProp :=
  SubNatRel (FR tt) (FL ImportedSumSequence.Unit_unit).

Definition ss_unit_nat_fun_to_imported (F : unit -> nat) :
    ImportedSumSequence.Unit -> Lean.Nat :=
  fun _ => sub_nat_to_imported (F tt).

Definition ss_unit_nat_fun_to_rocq
    (F : ImportedSumSequence.Unit -> Lean.Nat) : unit -> nat :=
  fun _ => sub_nat_to_rocq (F ImportedSumSequence.Unit_unit).

Lemma ss_unit_nat_fun_canonical (F : unit -> nat) :
  SsUnitNatFunRel F (ss_unit_nat_fun_to_imported F).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma ss_unit_nat_fun_surjective
    (F : ImportedSumSequence.Unit -> Lean.Nat) :
  SsUnitNatFunRel (ss_unit_nat_fun_to_rocq F) F.
Proof. exact (sub_nat_imported_roundtrip (F ImportedSumSequence.Unit_unit)). Qed.

Lemma ss_source_unit_sum_eq (F : unit -> nat) :
  Logic.eq (\sum_r F r) (F tt).
Proof.
  rewrite /index_enum unlock_with -enumT /=.
  have -> : enum (unit : finType) = [:: tt]
    by rewrite /(enum _) unlock //=.
  by rewrite big_seq1.
Qed.

Lemma ss_target_unit_sum_eq
    (F : ImportedSumSequence.Unit -> Lean.Nat) :
  Lean.eq (ss_target_unit_sum F) (F ImportedSumSequence.Unit_unit).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma ss_unit_sum_related (FR : unit -> nat)
    (FL : ImportedSumSequence.Unit -> Lean.Nat) :
  SsUnitNatFunRel FR FL ->
  SubNatRel (\sum_r FR r) (ss_target_unit_sum FL).
Proof.
  intro HF. unfold SubNatRel.
  rewrite (ss_source_unit_sum_eq FR).
  exact (sub_imported_eq_trans _ _ _ HF
    (sub_imported_eq_sym _ _ (ss_target_unit_sum_eq FL))).
Qed.

Lemma ss_sum_unit1_instance_correspondence (FR : unit -> nat)
    (FL : ImportedSumSequence.Unit -> Lean.Nat) :
  SsUnitNatFunRel FR FL ->
  PropSPropRel
    (Logic.eq (\sum_r FR r) (FR tt))
    (Lean.eq (ss_target_unit_sum FL)
      (FL ImportedSumSequence.Unit_unit)).
Proof.
  intro HF. apply sub_nat_eq_correspondence.
  - exact (ss_unit_sum_related FR FL HF).
  - exact HF.
Qed.

(** Logical and small-Nat operation layer for [sum_ge_2_seq]. *)
Definition ss_target_one : Lean.Nat :=
  ImportedSumSequence.OfNat_ofNat_inst1 Lean.Nat
    (Lean.Nat_succ Lean.Nat_zero)
    (ImportedSumSequence.instOfNatNat (Lean.Nat_succ Lean.Nat_zero)).

Definition ss_target_two : Lean.Nat :=
  ImportedSumSequence.OfNat_ofNat_inst1 Lean.Nat
    (Lean.Nat_succ (Lean.Nat_succ Lean.Nat_zero))
    (ImportedSumSequence.instOfNatNat
      (Lean.Nat_succ (Lean.Nat_succ Lean.Nat_zero))).

Lemma ss_one_related : SubNatRel 1%N ss_target_one.
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma ss_two_related : SubNatRel 2%N ss_target_two.
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma ss_and_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P /\ Q) (Lean.And PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [p q]. exact (Lean.And_intro _ _
      (prop_to_sprop _ _ HP p) (prop_to_sprop _ _ HQ q)).
  - intros [p q]. apply strictly_inhabits. split.
    + exact (sprop_to_prop _ _ HP p).
    + exact (sprop_to_prop _ _ HQ q).
Qed.

Lemma ss_exists_identity_correspondence (T : Type)
    (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (exists x, PR x) (ImportedSumSequence.Exists T PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (ImportedSumSequence.Exists_intro T PL x
      (prop_to_sprop _ _ (HP x) Hx)).
  - intros [x Hx]. apply strictly_inhabits. exists x.
    exact (sprop_to_prop _ _ (HP x) Hx).
Qed.

Lemma ss_pointwise_le_one_correspondence (T : eqType)
    (xsR : seq T) (xsL : ImportedSumSequence.List T)
    (pR : T -> nat) (pL : T -> Lean.Nat) :
  SsListRel xsR xsL -> SsNatFunRel pR pL ->
  PropSPropRel
    (forall x, x \in xsR -> is_true (leq (pR x) 1%N))
    (forall x, ss_target_mem x xsL -> ss_target_le (pL x) ss_target_one).
Proof.
  intros Hxs Hp. apply prop_sprop_rel_intro.
  - intros HR x HmemL. apply (prop_to_sprop _ _
      (ss_le_correspondence _ _ _ _ (Hp x) ss_one_related)).
    apply HR. exact (sprop_to_prop _ _
      (ss_membership_correspondence T x xsR xsL Hxs) HmemL).
  - intro HL. apply strictly_inhabits. intros x HmemR.
    apply (sprop_to_prop _ _
      (ss_le_correspondence _ _ _ _ (Hp x) ss_one_related)).
    apply HL. exact (prop_to_sprop _ _
      (ss_membership_correspondence T x xsR xsL Hxs) HmemR).
Qed.

Lemma ss_ge_two_correspondence nR nL :
  SubNatRel nR nL ->
  PropSPropRel (is_true (ltn 1%N nR)) (ss_target_le ss_target_two nL).
Proof.
  intro Hn.
  exact (ss_lt_correspondence 1%N ss_target_one nR nL ss_one_related Hn).
Qed.

Lemma ss_sum_ge_2_conclusion_correspondence (T : eqType)
    (xsR : seq T) (xsL : ImportedSumSequence.List T)
    (pR : T -> nat) (pL : T -> Lean.Nat) :
  SsListRel xsR xsL -> SsNatFunRel pR pL ->
  PropSPropRel
    (exists x1 x2 : T,
      x1 != x2 /\ x1 \in xsR /\ x2 \in xsR /\
      pR x1 == 1%N /\ pR x2 == 1%N)
    (ImportedSumSequence.Exists T (fun x1 =>
      ImportedSumSequence.Exists T (fun x2 =>
        Lean.And
          (Lean.eq (ss_target_decide_ne T x1 x2)
            ImportedSumSequence.Bool_true)
          (Lean.And (ss_target_mem x1 xsL)
            (Lean.And (ss_target_mem x2 xsL)
              (Lean.And
                (Lean.eq (ss_target_decide_nat_eq (pL x1) ss_target_one)
                  ImportedSumSequence.Bool_true)
                (Lean.eq (ss_target_decide_nat_eq (pL x2) ss_target_one)
                  ImportedSumSequence.Bool_true))))))).
Proof.
  intros Hxs Hp. apply ss_exists_identity_correspondence. intro x1.
  apply ss_exists_identity_correspondence. intro x2.
  apply ss_and_correspondence.
  - exact (ss_bool_true_correspondence _ _
      (ss_decide_ne_related T x1 x2)).
  - apply ss_and_correspondence.
    + exact (ss_membership_correspondence T x1 xsR xsL Hxs).
    + apply ss_and_correspondence.
      * exact (ss_membership_correspondence T x2 xsR xsL Hxs).
      * apply ss_and_correspondence.
        -- exact (ss_bool_true_correspondence _ _
             (ss_decide_nat_eq_related (pR x1) (pL x1)
               1%N ss_target_one (Hp x1) ss_one_related)).
        -- exact (ss_bool_true_correspondence _ _
             (ss_decide_nat_eq_related (pR x2) (pL x2)
               1%N ss_target_one (Hp x2) ss_one_related)).
Qed.

Lemma ss_sum_ge_2_seq_instance_correspondence (T : eqType)
    (xsR : seq T) (xsL : ImportedSumSequence.List T)
    (pR : T -> nat) (pL : T -> Lean.Nat) :
  SsListRel xsR xsL -> SsNatFunRel pR pL ->
  PropSPropRel
    (uniq xsR ->
      (forall x, x \in xsR -> is_true (leq (pR x) 1%N)) ->
      is_true (ltn 1%N (\sum_(x <- xsR) pR x)) ->
      exists x1 x2 : T,
        x1 != x2 /\ x1 \in xsR /\ x2 \in xsR /\
        pR x1 == 1%N /\ pR x2 == 1%N)
    (ImportedSumSequence.List_Nodup T xsL ->
      (forall x, ss_target_mem x xsL ->
        ss_target_le (pL x) ss_target_one) ->
      ss_target_le ss_target_two (ss_target_sumSeq xsL pL) ->
      ImportedSumSequence.Exists T (fun x1 =>
        ImportedSumSequence.Exists T (fun x2 =>
          Lean.And
            (Lean.eq (ss_target_decide_ne T x1 x2)
              ImportedSumSequence.Bool_true)
            (Lean.And (ss_target_mem x1 xsL)
              (Lean.And (ss_target_mem x2 xsL)
                (Lean.And
                  (Lean.eq (ss_target_decide_nat_eq (pL x1) ss_target_one)
                    ImportedSumSequence.Bool_true)
                  (Lean.eq (ss_target_decide_nat_eq (pL x2) ss_target_one)
                    ImportedSumSequence.Bool_true))))))).
Proof.
  intros Hxs Hp. apply ss_imp_correspondence.
  - exact (ss_uniq_correspondence T xsR xsL Hxs).
  - apply ss_imp_correspondence.
    + exact (ss_pointwise_le_one_correspondence T xsR xsL pR pL Hxs Hp).
    + apply ss_imp_correspondence.
      * apply ss_ge_two_correspondence.
        exact (ss_sumSeq_related T pR pL xsR xsL Hp Hxs).
      * exact (ss_sum_ge_2_conclusion_correspondence T xsR xsL pR pL
          Hxs Hp).
Qed.

Print Assumptions ss_bool_eq_correspondence.
Print Assumptions ss_membership_correspondence.
Print Assumptions ss_decide_nat_eq_related.
Print Assumptions ss_decide_lt_related.
Print Assumptions ss_decide_bool_true_related.
Print Assumptions ss_decide_eq_related.
Print Assumptions ss_decide_ne_related.
Print Assumptions ss_filter_related.
Print Assumptions ss_length_related.
Print Assumptions ss_all_related.
Print Assumptions ss_any_related.
Print Assumptions ss_all_filter_imp_related.
Print Assumptions ss_any_filter_and_related.
Print Assumptions ss_sumSeq_related.
Print Assumptions ss_sumFiltered_related.
Print Assumptions ss_maxFiltered_related.
Print Assumptions ss_subseqb_related.
Print Assumptions ss_imp_correspondence.
Print Assumptions ss_pointwise_le_correspondence.
Print Assumptions ss_pointwise_pred_imp_correspondence.
Print Assumptions ss_pointwise_bool_split_correspondence.
Print Assumptions ss_pointwise_bool_exclusive_correspondence.
Print Assumptions ss_pointwise_nat_eq_bool_correspondence.
Print Assumptions ss_subset_correspondence.
Print Assumptions ss_uniq_correspondence.
Print Assumptions ss_subseq_truth_correspondence.
Print Assumptions ss_sum_le_subseq_instance_correspondence.
Print Assumptions ss_leq_sum_sub_uniq_instance_correspondence.
Print Assumptions ss_filtered_sum_le_correspondence.
Print Assumptions ss_sumFiltered_le_correspondence.
Print Assumptions ss_filtered_sum_eq_correspondence.
Print Assumptions ss_leq_sum_seq_instance_correspondence.
Print Assumptions ss_eq_sum_seq_instance_correspondence.
Print Assumptions ss_leq_sum_seq_pred_instance_correspondence.
Print Assumptions ss_ltn_sum_leq_seq_instance_correspondence.
Print Assumptions ss_eq_sum_leq_seq_instance_correspondence.
Print Assumptions ss_sum_split_instance_correspondence.
Print Assumptions ss_sumOfPartition_related.
Print Assumptions ss_sumOverPartitions_related.
Print Assumptions ss_partition_covered_correspondence.
Print Assumptions ss_sum_over_partitions_le_instance_correspondence.
Print Assumptions ss_sum_over_partitions_eq_instance_correspondence.
Print Assumptions ss_reorder_summation_result_correspondence.
Print Assumptions ss_reorder_summation_instance_correspondence.
Print Assumptions ss_decide_le_related.
Print Assumptions ss_nat_endofun_canonical.
Print Assumptions ss_nat_endofun_surjective.
Print Assumptions ss_monotone_correspondence.
Print Assumptions ss_pointwise_monotone_correspondence.
Print Assumptions ss_filtered_family_sum_related.
Print Assumptions ss_sum_leq_mono_instance_correspondence.
Print Assumptions ss_target_unit_sum_eq.
Print Assumptions ss_unit_sum_related.
Print Assumptions ss_sum_unit1_instance_correspondence.
Print Assumptions ss_one_related.
Print Assumptions ss_two_related.
Print Assumptions ss_and_correspondence.
Print Assumptions ss_exists_identity_correspondence.
Print Assumptions ss_pointwise_le_one_correspondence.
Print Assumptions ss_ge_two_correspondence.
Print Assumptions ss_sum_ge_2_conclusion_correspondence.
Print Assumptions ss_sum_ge_2_seq_instance_correspondence.
