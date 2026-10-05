From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedListLast.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  ListLastCertificate.
From prosa Require Import GeneratedListLastSource.

(** Actual-artifact adapter for the approved representation boundary
    [eqType] -> carrier [Type] plus the corresponding Lean [DecidableEq]. *)
Definition lr_decidable_eq (T : eqType) : ImportedListLast.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => ImportedListLast.Decidable_isTrue (Lean.eq x y)
        (coq_eq_to_imported_eq x y H)
    | ReflectF H => ImportedListLast.Decidable_isFalse (Lean.eq x y)
        (fun HL => ll_coq_false_to_target
          (H (imported_eq_to_coq_eq x y HL)))
    end.

Fixpoint lr_to_imported {T : Type} (xs : seq T) :
    ImportedListLast.List T :=
  match xs with
  | [::] => ImportedListLast.List_nil T
  | x :: xs' => ImportedListLast.List_cons T x (lr_to_imported xs')
  end.

Fixpoint lr_to_rocq {T : Type} (xs : ImportedListLast.List T) : seq T :=
  match xs with
  | ImportedListLast.List_nil => [::]
  | ImportedListLast.List_cons x xs' => x :: lr_to_rocq xs'
  end.

Definition LrListRel {T : Type} (xsR : seq T)
    (xsL : ImportedListLast.List T) : SProp :=
  Lean.eq (lr_to_imported xsR) xsL.

Lemma lr_source_roundtrip {T : Type} (xs : seq T) :
  Logic.eq (lr_to_rocq (lr_to_imported xs)) xs.
Proof. induction xs; cbn; first reflexivity. f_equal. exact IHxs. Qed.

Lemma lr_target_roundtrip {T : Type} (xs : ImportedListLast.List T) :
  Lean.eq (lr_to_imported (lr_to_rocq xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (@Lean.eq_refl _ (ImportedListLast.List_nil T)).
  - exact (sub_imported_eq_congr
      (ImportedListLast.List_cons T x) _ _ IH).
Qed.

Definition lr_target_mem {T : Type} (x : T)
    (xs : ImportedListLast.List T) : SProp :=
  ImportedListLast.Membership_mem T (ImportedListLast.List T)
    (ImportedListLast.List_instMembership T) xs x.

Definition lr_list_mem_transport {T : Type} (x : T)
    (xs ys : ImportedListLast.List T) :
    Lean.eq xs ys -> ImportedListLast.List_Mem T x xs ->
    ImportedListLast.List_Mem T x ys :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ zs return ImportedListLast.List_Mem T x zs with
    | Lean.eq_refl => Hmem
    end.

Definition lr_mem_head_of_coq_eq {T : Type} (x y : T)
    (xs : ImportedListLast.List T) : Logic.eq x y ->
    ImportedListLast.List_Mem T x (ImportedListLast.List_cons T y xs) :=
  fun H => match H in Logic.eq _ z return
      ImportedListLast.List_Mem T x (ImportedListLast.List_cons T z xs)
    with
    | Logic.eq_refl => ImportedListLast.List_Mem_head T x xs
    end.

Definition lr_eq_refl_truth (T : eqType) (x : T) :
    SubNatTruth (x == x).
Proof. rw eqxx. exact sub_nat_truth_intro. Defined.

Fixpoint lr_seq_mem_forward {T : eqType} (x : T) (xs : seq T) :
    SubNatTruth (x \in xs) ->
    ImportedListLast.List_Mem T x (lr_to_imported xs) :=
  match xs as xs0 return SubNatTruth (x \in xs0) ->
      ImportedListLast.List_Mem T x (lr_to_imported xs0)
  with
  | [::] => sub_nat_false_elim _
  | y :: ys =>
      match @eqP T x y as r in reflect _ b return
        SubNatTruth (b || (x \in ys)) ->
        ImportedListLast.List_Mem T x
          (ImportedListLast.List_cons T y (lr_to_imported ys))
      with
      | ReflectT Hxy => fun _ => lr_mem_head_of_coq_eq x y _ Hxy
      | ReflectF _ => fun H => ImportedListLast.List_Mem_tail T x y _
          (lr_seq_mem_forward x ys H)
      end
  end.

Fixpoint lr_imported_mem_decoded {T : eqType} (x : T)
    (xs : ImportedListLast.List T)
    (H : ImportedListLast.List_Mem T x xs) :
    SubNatTruth (x \in lr_to_rocq xs) :=
  match H with
  | ImportedListLast.List_Mem_head ys =>
      ll_mem_head_truth _ _ (lr_eq_refl_truth T x)
  | ImportedListLast.List_Mem_tail y ys Htail =>
      ll_mem_tail_truth _ _ (lr_imported_mem_decoded x ys Htail)
  end.

Definition lr_mem_truth_transport {T : eqType} (x : T)
    (xs ys : seq T) : Logic.eq xs ys ->
    SubNatTruth (x \in xs) -> SubNatTruth (x \in ys) :=
  fun H Htruth =>
    match H in Logic.eq _ zs return
      SubNatTruth (x \in xs) -> SubNatTruth (x \in zs)
    with
    | Logic.eq_refl => fun Ht => Ht
    end Htruth.

Definition lr_imported_mem_backward {T : eqType} (x : T) (xs : seq T)
    (H : ImportedListLast.List_Mem T x (lr_to_imported xs)) :
    SubNatTruth (x \in xs) :=
  lr_mem_truth_transport x _ _ (lr_source_roundtrip xs)
    (lr_imported_mem_decoded x (lr_to_imported xs) H).

Lemma lr_membership_correspondence (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedListLast.List T) :
  LrListRel xsR xsL ->
  PropSPropRel (x \in xsR) (lr_target_mem x xsL).
Proof.
  intro Hlist. apply prop_sprop_rel_intro.
  - intro Hmem. unfold lr_target_mem.
    apply (lr_list_mem_transport x _ _ Hlist).
    apply lr_seq_mem_forward. exact (sub_nat_prop_to_truth _ Hmem).
  - intro Hmem. apply sub_nat_truth_to_strict_prop.
    apply lr_imported_mem_backward.
    unfold lr_target_mem in Hmem.
    exact (lr_list_mem_transport x _ _
      (sub_imported_eq_sym _ _ Hlist) Hmem).
Qed.

Definition lr_target_erase (T : eqType) (xs : ImportedListLast.List T)
    (y : T) : ImportedListLast.List T :=
  ImportedListLast.List_erase T
    (ImportedListLast.instBEqOfDecidableEq T (lr_decidable_eq T)) xs y.

Lemma lr_decide_eq_canonical (T : eqType) (x y : T) :
  Lean.eq
    (ImportedListLast.Decidable_decide (Lean.eq x y)
      (lr_decidable_eq T x y))
    (ll_bool_to_imported (x == y)).
Proof.
  unfold lr_decidable_eq.
  destruct (@eqP T x y); exact (@Lean.eq_refl _ _).
Qed.

Definition lr_erase_match {T : Type} (b : ImportedListLast.Bool)
    (a : T) (xs tail : ImportedListLast.List T) : ImportedListLast.List T :=
  ImportedListLast.Prosa_Validation_ListLastInterface_filter_cons_match_1
    (fun _ : ImportedListLast.Bool => ImportedListLast.List T) b
    (fun _ : ImportedListLast.Unit => xs)
    (fun _ : ImportedListLast.Unit => ImportedListLast.List_cons T a tail).

Lemma lr_erase_match_canonical {T : Type} (b : bool) (a : T)
    (xs tail : ImportedListLast.List T) :
  Lean.eq (lr_erase_match (ll_bool_to_imported b) a xs tail)
    (match b with
     | true => xs
     | false => ImportedListLast.List_cons T a tail
     end).
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Lemma lr_erase_canonical (T : eqType) (y : T) (xs : seq T) :
  Lean.eq (lr_target_erase T (lr_to_imported xs) y)
    (lr_to_imported (rem y xs)).
Proof.
  induction xs as [|a xs IH].
  - exact (ImportedListLast.Prosa_Validation_ListLastInterface_generic_erase_nil
      T (lr_decidable_eq T) y).
  - refine (sub_imported_eq_trans _ _ _
      (ImportedListLast.Prosa_Validation_ListLastInterface_generic_erase_cons
        T (lr_decidable_eq T) a (lr_to_imported xs) y) _).
    refine (sub_imported_eq_trans _ _ _
      (sub_imported_eq_congr
        (fun b => lr_erase_match b a (lr_to_imported xs)
          (lr_target_erase T (lr_to_imported xs) y)) _ _
        (lr_decide_eq_canonical T a y)) _).
    refine (sub_imported_eq_trans _ _ _
      (lr_erase_match_canonical (a == y) a (lr_to_imported xs)
        (lr_target_erase T (lr_to_imported xs) y)) _).
    destruct (@eqP T a y) as [Heq | Hneq].
    + subst a. rewrite /rem eqxx. exact (@Lean.eq_refl _ _).
    + have Hneqb : a != y by apply/eqP.
      rewrite /rem (negbTE Hneqb).
      exact (sub_imported_eq_congr
        (ImportedListLast.List_cons T a) _ _ IH).
Qed.

Lemma lr_erase_related (T : eqType) (y : T)
    (xsR : seq T) (xsL : ImportedListLast.List T) :
  LrListRel xsR xsL ->
  LrListRel (rem y xsR) (lr_target_erase T xsL y).
Proof.
  intro Hxs. unfold LrListRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (lr_erase_canonical T y xsR))
    (sub_imported_eq_congr (fun zs => lr_target_erase T zs y) _ _ Hxs)).
Qed.

Definition lr_target_ne {T : Type} (x y : T) : SProp :=
  ImportedListLast.Ne T x y.

Lemma lr_neq_correspondence (T : eqType) (x y : T) :
  PropSPropRel (x != y) (lr_target_ne x y).
Proof.
  apply prop_sprop_rel_intro.
  - intro Hsrc. unfold lr_target_ne.
    intro HeqL. apply ll_coq_false_to_target.
    have Heq := imported_eq_to_coq_eq x y HeqL.
    subst y. move: Hsrc. rewrite eqxx. done.
  - intro Htarget. apply strictly_inhabits.
    apply/negP => /eqP Heq.
    exact (interpret_strict Logic.False
        (ll_false_to_strict
          (Htarget (coq_eq_to_imported_eq x y Heq)))).
Qed.

Definition lr_target_rem_in_statement : SProp :=
  forall (T : eqType) (x y : T) (xs : ImportedListLast.List T),
    lr_target_mem x (lr_target_erase T xs y) -> lr_target_mem x xs.

Definition lr_target_in_neq_impl_rem_in_statement : SProp :=
  forall (T : eqType) (x y : T) (xs : ImportedListLast.List T),
    lr_target_mem x xs -> lr_target_ne x y ->
    lr_target_mem x (lr_target_erase T xs y).

Theorem rem_in_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_rem_in
    lr_target_rem_in_statement.
Proof.
  unfold GeneratedListLastSource.statement_rem_in,
    lr_target_rem_in_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T x y xsL HmemL.
    have Hxs : LrListRel (lr_to_rocq xsL) xsL := lr_target_roundtrip xsL.
    have Herase := lr_erase_related T y _ _ Hxs.
    have HmemR := sprop_to_prop _ _
      (lr_membership_correspondence T x _ _ Herase) HmemL.
    exact (prop_to_sprop _ _
      (lr_membership_correspondence T x _ _ Hxs)
      (Hsource T x y (lr_to_rocq xsL) HmemR)).
  - intro Htarget. apply strictly_inhabits.
    intros T x y xsR HmemR.
    have Hxs : LrListRel xsR (lr_to_imported xsR) :=
      @Lean.eq_refl _ (lr_to_imported xsR).
    have Herase := lr_erase_related T y _ _ Hxs.
    have HmemL := prop_to_sprop _ _
      (lr_membership_correspondence T x _ _ Herase) HmemR.
    exact (sprop_to_prop _ _
      (lr_membership_correspondence T x _ _ Hxs)
      (Htarget T x y (lr_to_imported xsR) HmemL)).
Qed.

Theorem in_neq_impl_rem_in_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_in_neq_impl_rem_in
    lr_target_in_neq_impl_rem_in_statement.
Proof.
  unfold GeneratedListLastSource.statement_in_neq_impl_rem_in,
    lr_target_in_neq_impl_rem_in_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T x y xsL HmemL HneqL.
    have Hxs : LrListRel (lr_to_rocq xsL) xsL := lr_target_roundtrip xsL.
    have HmemR := sprop_to_prop _ _
      (lr_membership_correspondence T x _ _ Hxs) HmemL.
    have HneqR := sprop_to_prop _ _ (lr_neq_correspondence T x y) HneqL.
    have Herase := lr_erase_related T y _ _ Hxs.
    exact (prop_to_sprop _ _
      (lr_membership_correspondence T x _ _ Herase)
      (Hsource T x y (lr_to_rocq xsL) HmemR HneqR)).
  - intro Htarget. apply strictly_inhabits.
    intros T x y xsR HmemR HneqR.
    have Hxs : LrListRel xsR (lr_to_imported xsR) :=
      @Lean.eq_refl _ (lr_to_imported xsR).
    have HmemL := prop_to_sprop _ _
      (lr_membership_correspondence T x _ _ Hxs) HmemR.
    have HneqL := prop_to_sprop _ _ (lr_neq_correspondence T x y) HneqR.
    have Herase := lr_erase_related T y _ _ Hxs.
    exact (sprop_to_prop _ _
      (lr_membership_correspondence T x _ _ Herase)
      (Htarget T x y (lr_to_imported xsR) HmemL HneqL)).
Qed.

(** The filter/length part of [filter_size_rem] uses the same representation
    maps.  Predicates remain Boolean computations on both sides. *)
Definition LrPredRel {T : Type} (PR : T -> bool)
    (PL : T -> ImportedListLast.Bool) : SProp :=
  forall x, Lean.eq (ll_bool_to_imported (PR x)) (PL x).

Definition lr_pred_to_imported {T : Type} (PR : T -> bool) :
    T -> ImportedListLast.Bool :=
  fun x => ll_bool_to_imported (PR x).

Definition lr_pred_to_rocq {T : Type}
    (PL : T -> ImportedListLast.Bool) : T -> bool :=
  fun x => ll_bool_to_rocq (PL x).

Lemma lr_pred_canonical {T : Type} (PR : T -> bool) :
  LrPredRel PR (lr_pred_to_imported PR).
Proof. intro x. exact (@Lean.eq_refl _ _). Qed.

Lemma lr_pred_surjective {T : Type}
    (PL : T -> ImportedListLast.Bool) :
  LrPredRel (lr_pred_to_rocq PL) PL.
Proof. intro x. exact (ll_bool_imported_roundtrip (PL x)). Qed.

Definition lr_target_filter {T : Type}
    (P : T -> ImportedListLast.Bool) (xs : ImportedListLast.List T) :
    ImportedListLast.List T := ImportedListLast.List_filter T P xs.

Definition lr_filter_match {T : Type} (b : ImportedListLast.Bool)
    (a : T) (tail : ImportedListLast.List T) : ImportedListLast.List T :=
  ImportedListLast.Prosa_Validation_ListLastInterface_filter_cons_match_1
    (fun _ : ImportedListLast.Bool => ImportedListLast.List T) b
    (fun _ : ImportedListLast.Unit => ImportedListLast.List_cons T a tail)
    (fun _ : ImportedListLast.Unit => tail).

Lemma lr_filter_match_canonical {T : Type} (b : bool) (a : T)
    (tail : ImportedListLast.List T) :
  Lean.eq (lr_filter_match (ll_bool_to_imported b) a tail)
    (match b with
     | true => ImportedListLast.List_cons T a tail
     | false => tail
     end).
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Lemma lr_filter_branch_canonical {T : Type} (b : bool) (a : T)
    (filtered : seq T) (tail : ImportedListLast.List T) :
  Lean.eq tail (lr_to_imported filtered) ->
  Lean.eq
    (match b with
     | true => ImportedListLast.List_cons T a tail
     | false => tail
     end)
    (lr_to_imported
      (match b with true => a :: filtered | false => filtered end)).
Proof.
  intro IH. destruct b; cbn.
  - exact (sub_imported_eq_congr (ImportedListLast.List_cons T a) _ _ IH).
  - exact IH.
Qed.

Lemma lr_source_filter_cons {T : Type} (P : T -> bool)
    (a : T) (xs : seq T) :
  Logic.eq
    (match P a with
     | true => a :: [seq x <- xs | P x]
     | false => [seq x <- xs | P x]
     end)
    [seq x <- a :: xs | P x].
Proof. cbn. destruct (P a); reflexivity. Qed.

Lemma lr_filter_with_pred_canonical (T : Type) (PR : T -> bool)
    (PL : T -> ImportedListLast.Bool) : LrPredRel PR PL ->
  forall xs : seq T,
  Lean.eq (lr_target_filter PL (lr_to_imported xs))
    (lr_to_imported [seq x <- xs | PR x]).
Proof.
  intro HP. induction xs as [|a xs IH].
  - exact (ImportedListLast.Prosa_Validation_ListLastInterface_generic_filter_nil
      T PL).
  - refine (sub_imported_eq_trans _ _ _
      (ImportedListLast.Prosa_Validation_ListLastInterface_generic_filter_cons
        T PL a (lr_to_imported xs)) _).
    refine (sub_imported_eq_trans _ _ _
      (sub_imported_eq_congr
        (fun b => lr_filter_match b a
          (lr_target_filter PL (lr_to_imported xs))) _ _
        (sub_imported_eq_sym _ _ (HP a))) _).
    refine (sub_imported_eq_trans _ _ _
      (lr_filter_match_canonical (PR a) a
        (lr_target_filter PL (lr_to_imported xs))) _).
    refine (sub_imported_eq_trans _ _ _
      (lr_filter_branch_canonical (PR a) a
        [seq x <- xs | PR x] (lr_target_filter PL (lr_to_imported xs)) IH) _).
    exact (coq_eq_to_imported_eq _ _
      (f_equal lr_to_imported (lr_source_filter_cons PR a xs))).
Qed.

Lemma lr_filter_related (T : Type) (PR : T -> bool)
    (PL : T -> ImportedListLast.Bool) (xsR : seq T)
    (xsL : ImportedListLast.List T) :
  LrPredRel PR PL -> LrListRel xsR xsL ->
  LrListRel [seq x <- xsR | PR x] (lr_target_filter PL xsL).
Proof.
  intros HP Hxs. unfold LrListRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _
      (lr_filter_with_pred_canonical T PR PL HP xsR))
    (sub_imported_eq_congr (lr_target_filter PL) _ _ Hxs)).
Qed.

Definition lr_target_length {T : Type}
    (xs : ImportedListLast.List T) : Lean.Nat :=
  ImportedListLast.List_length T xs.

Lemma lr_length_canonical (T : Type) (xs : seq T) :
  SubNatRel (size xs) (lr_target_length (lr_to_imported xs)).
Proof.
  induction xs as [|a xs IH].
  - exact (sub_imported_eq_sym _ _
      (sub_imported_eq_trans _ _ _
        (ImportedListLast.Prosa_Validation_ListLastInterface_generic_length_nil
          T)
        ImportedListLast.Prosa_Validation_ListLastInterface_nat_zero)).
  - unfold SubNatRel in IH |- *.
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_congr Lean.Nat_succ _ _ IH)
      (sub_imported_eq_sym _ _
        (ImportedListLast.Prosa_Validation_ListLastInterface_generic_length_cons
          T a (lr_to_imported xs)))).
Qed.

Lemma lr_length_related (T : Type) (xsR : seq T)
    (xsL : ImportedListLast.List T) : LrListRel xsR xsL ->
  SubNatRel (size xsR) (lr_target_length xsL).
Proof.
  intro Hxs. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _ (lr_length_canonical T xsR)
    (sub_imported_eq_congr lr_target_length _ _ Hxs)).
Qed.

Definition lr_target_add (a b : Lean.Nat) : Lean.Nat :=
  ImportedListLast.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedListLast.instHAdd_inst1 Lean.Nat ImportedListLast.instAddNat) a b.

Lemma lr_add_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR + bR) (lr_target_add aL bL).
Proof.
  intros Ha Hb. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (sub_add_canonical aR bR))
    (sub_imported_eq_congr2 lr_target_add _ _ _ _ Ha Hb)).
Qed.

Lemma lr_one_related : SubNatRel 1 ll_target_one.
Proof.
  exact (sub_imported_eq_sym _ _
    ImportedListLast.Prosa_Validation_ListLastInterface_nat_one).
Qed.

Definition lr_target_filter_size_rem_statement : SProp :=
  forall (T : eqType) (x : T) (xs : ImportedListLast.List T)
    (P : T -> ImportedListLast.Bool),
    lr_target_mem x xs ->
    Lean.eq (P x) ImportedListLast.Bool_true ->
    Lean.eq (lr_target_length (lr_target_filter P xs))
      (lr_target_add
        (lr_target_length
          (lr_target_filter P (lr_target_erase T xs x)))
        ll_target_one).

Theorem filter_size_rem_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_filter_size_rem
    lr_target_filter_size_rem_statement.
Proof.
  unfold GeneratedListLastSource.statement_filter_size_rem,
    lr_target_filter_size_rem_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T x xsL PL HmemL HPxL.
    pose PR := lr_pred_to_rocq PL.
    pose xsR := lr_to_rocq xsL.
    have Hpred : LrPredRel PR PL := lr_pred_surjective PL.
    have Hxs : LrListRel xsR xsL := lr_target_roundtrip xsL.
    have HmemR := sprop_to_prop _ _
      (lr_membership_correspondence T x _ _ Hxs) HmemL.
    have HPxR := sprop_to_prop _ _
      (ll_bool_true_correspondence (PR x) (PL x) (Hpred x)) HPxL.
    have HsourceEq := Hsource T x xsR PR HmemR HPxR.
    have Herase := lr_erase_related T x _ _ Hxs.
    have Hfilter := lr_filter_related T PR PL _ _ Hpred Hxs.
    have HfilterErase := lr_filter_related T PR PL _ _ Hpred Herase.
    have Hlen := lr_length_related T _ _ Hfilter.
    have HlenErase := lr_length_related T _ _ HfilterErase.
    have Hadd := lr_add_related _ _ 1 ll_target_one HlenErase lr_one_related.
    exact (prop_to_sprop _ _
      (sub_nat_eq_correspondence _ _ _ _ Hlen Hadd) HsourceEq).
  - intro Htarget. apply strictly_inhabits.
    intros T x xsR PR HmemR HPxR.
    have Hpred : LrPredRel PR (lr_pred_to_imported PR) :=
      lr_pred_canonical PR.
    have Hxs : LrListRel xsR (lr_to_imported xsR) :=
      @Lean.eq_refl _ (lr_to_imported xsR).
    have HmemL := prop_to_sprop _ _
      (lr_membership_correspondence T x _ _ Hxs) HmemR.
    have HPxL := prop_to_sprop _ _
      (ll_bool_true_correspondence (PR x)
        (lr_pred_to_imported PR x) (Hpred x)) HPxR.
    have HtargetEq := Htarget T x (lr_to_imported xsR)
      (lr_pred_to_imported PR) HmemL HPxL.
    have Herase := lr_erase_related T x _ _ Hxs.
    have Hfilter := lr_filter_related T PR (lr_pred_to_imported PR)
      _ _ Hpred Hxs.
    have HfilterErase := lr_filter_related T PR (lr_pred_to_imported PR)
      _ _ Hpred Herase.
    have Hlen := lr_length_related T _ _ Hfilter.
    have HlenErase := lr_length_related T _ _ HfilterErase.
    have Hadd := lr_add_related _ _ 1 ll_target_one HlenErase lr_one_related.
    exact (sprop_to_prop _ _
      (sub_nat_eq_correspondence _ _ _ _ Hlen Hadd) HtargetEq).
Qed.

(** [undup] and Lean [eraseDups] do not have to be related as ordered lists
    for this declaration: its observable is Boolean membership.  The following
    relation is therefore deliberately extensional.  The target operation
    lemma is exported with its actual Lean proof body and rechecked by Rocq;
    it is not the Prosa theorem under validation. *)
Definition lr_target_erase_dups (T : eqType)
    (xs : ImportedListLast.List T) : ImportedListLast.List T :=
  ImportedListLast.List_eraseDups T
    (ImportedListLast.instBEqOfDecidableEq T (lr_decidable_eq T)) xs.

Definition lr_target_mem_decidable (T : eqType) (x : T)
    (xs : ImportedListLast.List T) :
    ImportedListLast.Decidable (lr_target_mem x xs) :=
  ImportedListLast.List_instDecidableMemOfLawfulBEq T
    (ImportedListLast.instBEqOfDecidableEq T (lr_decidable_eq T))
    (ImportedListLast.instLawfulBEq T (lr_decidable_eq T)) x xs.

Definition lr_target_decide_mem (T : eqType) (x : T)
    (xs : ImportedListLast.List T) : ImportedListLast.Bool :=
  ImportedListLast.Decidable_decide (lr_target_mem x xs)
    (lr_target_mem_decidable T x xs).

Lemma lr_target_mem_erase_dups_iff (T : eqType) (x : T)
    (xs : ImportedListLast.List T) :
  ImportedListLast.Iff
    (lr_target_mem x (lr_target_erase_dups T xs))
    (lr_target_mem x xs).
Proof.
  exact
    (ImportedListLast.Prosa_Validation_ListLastInterface_generic_mem_eraseDups
      T (lr_decidable_eq T) x xs).
Qed.

Definition lr_bool_false_elim (H : is_true false) : Logic.False.
Proof. discriminate H. Defined.

Lemma lr_decide_bool_correspondence (b : bool) (Q : SProp)
    (d : ImportedListLast.Decidable Q) :
  PropSPropRel (is_true b) Q ->
  LlBoolRel b (ImportedListLast.Decidable_decide Q d).
Proof.
  intro Hrel. unfold LlBoolRel.
  destruct d as [Hfalse | Htrue]; destruct b; cbn.
  - exact (ll_false_elim _
      (Hfalse (prop_to_sprop _ _ Hrel (Logic.eq_refl true)))).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - exact (ll_false_elim _ (ll_coq_false_to_target
      (lr_bool_false_elim (sprop_to_prop _ _ Hrel Htrue)))).
Qed.

Lemma lr_bool_eq_correspondence bR bL cR cL :
  LlBoolRel bR bL -> LlBoolRel cR cL ->
  PropSPropRel (Logic.eq bR cR) (Lean.eq bL cL).
Proof.
  intros Hb Hc. apply prop_sprop_rel_intro.
  - intro Heq. destruct Heq.
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _ Hb) Hc).
  - intro Heq. apply strictly_inhabits.
    have Hcanonical : Lean.eq (ll_bool_to_imported bR)
        (ll_bool_to_imported cR) :=
      sub_imported_eq_trans _ _ _ Hb
        (sub_imported_eq_trans _ _ _ Heq (sub_imported_eq_sym _ _ Hc)).
    have Hdecoded := f_equal ll_bool_to_rocq
      (imported_eq_to_coq_eq _ _ Hcanonical).
    rewrite (ll_bool_rocq_roundtrip bR) in Hdecoded.
    rewrite (ll_bool_rocq_roundtrip cR) in Hdecoded.
    exact Hdecoded.
Qed.

Lemma lr_undup_erase_dups_membership (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedListLast.List T) :
  LrListRel xsR xsL ->
  PropSPropRel (x \in undup xsR)
    (lr_target_mem x (lr_target_erase_dups T xsL)).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intro HmemUndup.
    have HmemR : x \in xsR.
    { move: HmemUndup. rewrite (mem_undup xsR x). done. }
    have HmemL := prop_to_sprop _ _
      (lr_membership_correspondence T x _ _ Hxs) HmemR.
    exact (ImportedListLast.Iff_mpr _ _
      (lr_target_mem_erase_dups_iff T x xsL) HmemL).
  - intro HmemDups. apply strictly_inhabits.
    have HmemL := ImportedListLast.Iff_mp _ _
      (lr_target_mem_erase_dups_iff T x xsL) HmemDups.
    have HmemR := sprop_to_prop _ _
      (lr_membership_correspondence T x _ _ Hxs) HmemL.
    move: HmemR. rewrite -(mem_undup xsR x). done.
Qed.

Lemma lr_undup_decide_related (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedListLast.List T) :
  LrListRel xsR xsL ->
  LlBoolRel (x \in undup xsR)
    (lr_target_decide_mem T x (lr_target_erase_dups T xsL)).
Proof.
  intro Hxs. apply lr_decide_bool_correspondence.
  exact (lr_undup_erase_dups_membership T x xsR xsL Hxs).
Qed.

Lemma lr_mem_decide_related (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedListLast.List T) :
  LrListRel xsR xsL ->
  LlBoolRel (x \in xsR) (lr_target_decide_mem T x xsL).
Proof.
  intro Hxs. apply lr_decide_bool_correspondence.
  exact (lr_membership_correspondence T x xsR xsL Hxs).
Qed.

Definition lr_target_in_seq_equiv_undup_statement : SProp :=
  forall (T : eqType) (xs : ImportedListLast.List T) (x : T),
    Lean.eq
      (lr_target_decide_mem T x (lr_target_erase_dups T xs))
      (lr_target_decide_mem T x xs).

Theorem in_seq_equiv_undup_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_in_seq_equiv_undup
    lr_target_in_seq_equiv_undup_statement.
Proof.
  unfold GeneratedListLastSource.statement_in_seq_equiv_undup,
    lr_target_in_seq_equiv_undup_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T xsL x.
    have Hxs : LrListRel (lr_to_rocq xsL) xsL := lr_target_roundtrip xsL.
    exact (prop_to_sprop _ _
      (lr_bool_eq_correspondence _ _ _ _
        (lr_undup_decide_related T x _ _ Hxs)
        (lr_mem_decide_related T x _ _ Hxs))
      (Hsource T (lr_to_rocq xsL) x)).
  - intro Htarget. apply strictly_inhabits.
    intros T xsR x.
    have Hxs : LrListRel xsR (lr_to_imported xsR) :=
      @Lean.eq_refl _ (lr_to_imported xsR).
    exact (sprop_to_prop _ _
      (lr_bool_eq_correspondence _ _ _ _
        (lr_undup_decide_related T x _ _ Hxs)
        (lr_mem_decide_related T x _ _ Hxs))
      (Htarget T (lr_to_imported xsR) x)).
Qed.

(** Reusable generic equality lifting for the next list cluster.  The source
    equality observation is MathComp Boolean equality; the target observation
    is the actual imported Lean [decide] for a related equality proposition. *)
Lemma lr_list_eq_correspondence {T : Type}
    (xsR ysR : seq T) (xsL ysL : ImportedListLast.List T) :
  LrListRel xsR xsL -> LrListRel ysR ysL ->
  PropSPropRel (Logic.eq xsR ysR) (Lean.eq xsL ysL).
Proof.
  intros Hxs Hys. apply prop_sprop_rel_intro.
  - intro Heq. destruct Heq.
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _ Hxs) Hys).
  - intro Heq. apply strictly_inhabits.
    have Hcanonical : Lean.eq (lr_to_imported xsR) (lr_to_imported ysR) :=
      sub_imported_eq_trans _ _ _ Hxs
        (sub_imported_eq_trans _ _ _ Heq
          (sub_imported_eq_sym _ _ Hys)).
    have Hdecoded := f_equal lr_to_rocq
      (imported_eq_to_coq_eq _ _ Hcanonical).
    rewrite (lr_source_roundtrip xsR) in Hdecoded.
    rewrite (lr_source_roundtrip ysR) in Hdecoded.
    exact Hdecoded.
Qed.

Definition lr_option_to_imported {T : Type} (o : option T) :
    ImportedListLast.Option T :=
  match o with
  | None => ImportedListLast.Option_none T
  | Some x => ImportedListLast.Option_some T x
  end.

Definition lr_option_to_rocq {T : Type} (o : ImportedListLast.Option T) :
    option T :=
  match o with
  | ImportedListLast.Option_none => None
  | ImportedListLast.Option_some x => Some x
  end.

Definition LrOptionRel {T : Type} (oR : option T)
    (oL : ImportedListLast.Option T) : SProp :=
  Lean.eq (lr_option_to_imported oR) oL.

Lemma lr_option_source_roundtrip {T : Type} (o : option T) :
  Logic.eq (lr_option_to_rocq (lr_option_to_imported o)) o.
Proof. destruct o; reflexivity. Qed.

Lemma lr_option_eq_correspondence {T : Type}
    (aR bR : option T) (aL bL : ImportedListLast.Option T) :
  LrOptionRel aR aL -> LrOptionRel bR bL ->
  PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof.
  intros Ha Hb. apply prop_sprop_rel_intro.
  - intro Heq. destruct Heq.
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _ Ha) Hb).
  - intro Heq. apply strictly_inhabits.
    have Hcanonical : Lean.eq (lr_option_to_imported aR)
        (lr_option_to_imported bR) :=
      sub_imported_eq_trans _ _ _ Ha
        (sub_imported_eq_trans _ _ _ Heq
          (sub_imported_eq_sym _ _ Hb)).
    have Hdecoded := f_equal lr_option_to_rocq
      (imported_eq_to_coq_eq _ _ Hcanonical).
    rewrite (lr_option_source_roundtrip aR) in Hdecoded.
    rewrite (lr_option_source_roundtrip bR) in Hdecoded.
    exact Hdecoded.
Qed.

Lemma lr_eqb_decide_from_eq_rel
    (AR : eqType) (AL : Type)
    (aR bR : AR) (aL bL : AL)
    (d : ImportedListLast.Decidable (Lean.eq aL bL)) :
  PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL) ->
  LlBoolRel (aR == bR) (ImportedListLast.Decidable_decide _ d).
Proof.
  intro Heq. apply lr_decide_bool_correspondence.
  apply prop_sprop_rel_intro.
  - intro Hbool. apply (prop_to_sprop _ _ Heq).
    by move/eqP: Hbool.
  - intro Htarget. apply strictly_inhabits. apply/eqP.
    exact (sprop_to_prop _ _ Heq Htarget).
Qed.

Definition lr_target_singleton_list_eq_decidable (T : eqType) (x y : T) :
    ImportedListLast.Decidable
      (Lean.eq
        (ImportedListLast.List_cons T x (ImportedListLast.List_nil T))
        (ImportedListLast.List_cons T y (ImportedListLast.List_nil T))) :=
  ImportedListLast.instDecidableEqList T (lr_decidable_eq T)
    (ImportedListLast.List_cons T x (ImportedListLast.List_nil T))
    (ImportedListLast.List_cons T y (ImportedListLast.List_nil T)).

Definition lr_target_singleton_list_eq_decide (T : eqType) (x y : T) :
    ImportedListLast.Bool :=
  ImportedListLast.Decidable_decide _
    (lr_target_singleton_list_eq_decidable T x y).

Definition lr_target_some_eq_decidable (T : eqType) (x y : T) :
    ImportedListLast.Decidable
      (Lean.eq (ImportedListLast.Option_some T x)
        (ImportedListLast.Option_some T y)) :=
  ImportedListLast.Option_instDecidableEq T (lr_decidable_eq T)
    (ImportedListLast.Option_some T x)
    (ImportedListLast.Option_some T y).

Definition lr_target_some_eq_decide (T : eqType) (x y : T) :
    ImportedListLast.Bool :=
  ImportedListLast.Decidable_decide _ (lr_target_some_eq_decidable T x y).

Lemma lr_seq1_list_equality_observation (T : eqType) (x y : T) :
  LlBoolRel ([:: x] == [:: y])
    (lr_target_singleton_list_eq_decide T x y).
Proof.
  apply lr_eqb_decide_from_eq_rel.
  apply lr_list_eq_correspondence;
    exact (@Lean.eq_refl _ _).
Qed.

Lemma lr_some_equality_observation (T : eqType) (x y : T) :
  LlBoolRel (Some x == Some y) (lr_target_some_eq_decide T x y).
Proof.
  apply lr_eqb_decide_from_eq_rel.
  apply lr_option_eq_correspondence;
    exact (@Lean.eq_refl _ _).
Qed.

Definition lr_target_seq1_some_statement : SProp :=
  forall (T : eqType) (x y : T),
    Lean.eq (lr_target_singleton_list_eq_decide T x y)
      (lr_target_some_eq_decide T x y).

Theorem seq1_some_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_seq1_some
    lr_target_seq1_some_statement.
Proof.
  unfold GeneratedListLastSource.statement_seq1_some,
    lr_target_seq1_some_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T x y.
    exact (prop_to_sprop _ _
      (lr_bool_eq_correspondence _ _ _ _
        (lr_seq1_list_equality_observation T x y)
        (lr_some_equality_observation T x y))
      (Hsource T x y)).
  - intro Htarget. apply strictly_inhabits. intros T x y.
    exact (sprop_to_prop _ _
      (lr_bool_eq_correspondence _ _ _ _
        (lr_seq1_list_equality_observation T x y)
        (lr_some_equality_observation T x y))
      (Htarget T x y)).
Qed.

(** Generic operation-level append correspondence, reused by existential list
    decomposition statements. *)
Definition lr_target_append {T : Type}
    (xs ys : ImportedListLast.List T) : ImportedListLast.List T :=
  ImportedListLast.List_append T xs ys.

Lemma lr_append_canonical (T : Type) (xs ys : seq T) :
  Lean.eq (lr_to_imported (xs ++ ys))
    (lr_target_append (lr_to_imported xs) (lr_to_imported ys)).
Proof.
  induction xs as [|x xs IH]; cbn [lr_target_append].
  - exact (@Lean.eq_refl _ (lr_to_imported ys)).
  - exact (sub_imported_eq_congr
      (ImportedListLast.List_cons T x) _ _ IH).
Qed.

Lemma lr_append_related (T : Type)
    (xsR ysR : seq T) (xsL ysL : ImportedListLast.List T) :
  LrListRel xsR xsL -> LrListRel ysR ysL ->
  LrListRel (xsR ++ ysR) (lr_target_append xsL ysL).
Proof.
  intros Hxs Hys. unfold LrListRel.
  exact (sub_imported_eq_trans _ _ _ (lr_append_canonical T xsR ysR)
    (sub_imported_eq_congr2 lr_target_append _ _ _ _ Hxs Hys)).
Qed.

Lemma lr_and_correspondence (P Q : Prop) (PL QL : SProp) :
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

Lemma lr_exists_identity_correspondence (T : Type)
    (PR : T -> Prop) (PL : T -> SProp) :
  (forall x, PropSPropRel (PR x) (PL x)) ->
  PropSPropRel (exists x, PR x) (ImportedListLast.Exists T PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [x Hx]. exact (ImportedListLast.Exists_intro T PL x
      (prop_to_sprop _ _ (HP x) Hx)).
  - intros [x Hx]. apply strictly_inhabits. exists x.
    exact (sprop_to_prop _ _ (HP x) Hx).
Qed.

Lemma lr_exists_list_correspondence (T : Type)
    (PR : seq T -> Prop) (PL : ImportedListLast.List T -> SProp) :
  (forall xsR xsL, LrListRel xsR xsL ->
    PropSPropRel (PR xsR) (PL xsL)) ->
  PropSPropRel (exists xsR, PR xsR)
    (ImportedListLast.Exists (ImportedListLast.List T) PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [xsR Hxs].
    exact (ImportedListLast.Exists_intro (ImportedListLast.List T) PL
      (lr_to_imported xsR)
      (prop_to_sprop _ _
        (HP xsR (lr_to_imported xsR) (@Lean.eq_refl _ _)) Hxs)).
  - intros [xsL Hxs]. apply strictly_inhabits.
    exists (lr_to_rocq xsL).
    exact (sprop_to_prop _ _
      (HP (lr_to_rocq xsL) xsL (lr_target_roundtrip xsL)) Hxs).
Qed.

Lemma lr_seq_elim_conclusion_correspondence (T : Type)
    (nR : nat) (nL : Lean.Nat)
    (xsR : seq T) (xsL : ImportedListLast.List T) :
  SubNatRel nR nL -> LrListRel xsR xsL ->
  PropSPropRel
    (exists (x : T) (pre : seq T),
      xsR = pre ++ [:: x] /\ size pre = nR)
    (ImportedListLast.Exists T (fun x =>
      ImportedListLast.Exists (ImportedListLast.List T) (fun pre =>
        Lean.And
          (Lean.eq xsL
            (lr_target_append pre
              (ImportedListLast.List_cons T x
                (ImportedListLast.List_nil T))))
          (Lean.eq (lr_target_length pre) nL)))).
Proof.
  intros Hn Hxs.
  apply lr_exists_identity_correspondence. intro x.
  apply lr_exists_list_correspondence. intros preR preL Hpre.
  apply lr_and_correspondence.
  - apply lr_list_eq_correspondence.
    + exact Hxs.
    + apply lr_append_related.
      * exact Hpre.
      * exact (@Lean.eq_refl _ _).
  - apply sub_nat_eq_correspondence.
    + exact (lr_length_related T preR preL Hpre).
    + exact Hn.
Qed.

Definition lr_target_seq_elim_last_statement : SProp :=
  forall (T : Type) (n : Lean.Nat) (xs : ImportedListLast.List T),
    Lean.eq (lr_target_length xs) (lr_target_add n ll_target_one) ->
    ImportedListLast.Exists T (fun x =>
      ImportedListLast.Exists (ImportedListLast.List T) (fun pre =>
        Lean.And
          (Lean.eq xs
            (lr_target_append pre
              (ImportedListLast.List_cons T x
                (ImportedListLast.List_nil T))))
          (Lean.eq (lr_target_length pre) n))).

Theorem seq_elim_last_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_seq_elim_last
    lr_target_seq_elim_last_statement.
Proof.
  unfold GeneratedListLastSource.statement_seq_elim_last,
    lr_target_seq_elim_last_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T nL xsL HlengthL.
    pose nR := sub_nat_to_rocq nL.
    pose xsR := lr_to_rocq xsL.
    have Hn : SubNatRel nR nL := sub_nat_rel_surjective nL.
    have Hxs : LrListRel xsR xsL := lr_target_roundtrip xsL.
    have Hlength := lr_length_related T xsR xsL Hxs.
    have Hsum := lr_add_related nR nL 1 ll_target_one Hn lr_one_related.
    have HlengthR := sprop_to_prop _ _
      (sub_nat_eq_correspondence _ _ _ _ Hlength Hsum) HlengthL.
    have HlengthRS : size xsR = nR.+1.
    { move: HlengthR. by rewrite addn1. }
    exact (prop_to_sprop _ _
      (lr_seq_elim_conclusion_correspondence T nR nL xsR xsL Hn Hxs)
      (Hsource T nR xsR HlengthRS)).
  - intro Htarget. apply strictly_inhabits.
    intros T nR xsR HlengthR.
    have HlengthRadd : size xsR = nR + 1.
    { move: HlengthR. by rewrite addn1. }
    have Hn : SubNatRel nR (sub_nat_to_imported nR) :=
      sub_nat_rel_canonical nR.
    have Hxs : LrListRel xsR (lr_to_imported xsR) :=
      @Lean.eq_refl _ _.
    have Hlength := lr_length_related T xsR (lr_to_imported xsR) Hxs.
    have Hsum := lr_add_related nR (sub_nat_to_imported nR)
      1 ll_target_one Hn lr_one_related.
    have HlengthL := prop_to_sprop _ _
      (sub_nat_eq_correspondence _ _ _ _ Hlength Hsum) HlengthRadd.
    exact (sprop_to_prop _ _
      (lr_seq_elim_conclusion_correspondence T nR
        (sub_nat_to_imported nR) xsR (lr_to_imported xsR) Hn Hxs)
      (Htarget T (sub_nat_to_imported nR)
        (lr_to_imported xsR) HlengthL)).
Qed.

Lemma lr_target_append_assoc (T : Type)
    (xs ys zs : ImportedListLast.List T) :
  Lean.eq (lr_target_append xs (lr_target_append ys zs))
    (lr_target_append (lr_target_append xs ys) zs).
Proof.
  induction xs as [|x xs IH]; cbn [lr_target_append].
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr
      (ImportedListLast.List_cons T x) _ _ IH).
Qed.

Lemma lr_in_cat_rhs_related (T : Type) (x : T)
    (leftR rightR : seq T)
    (leftL rightL : ImportedListLast.List T) :
  LrListRel leftR leftL -> LrListRel rightR rightL ->
  LrListRel (leftR ++ [:: x] ++ rightR)
    (lr_target_append
      (lr_target_append leftL
        (ImportedListLast.List_cons T x (ImportedListLast.List_nil T)))
      rightL).
Proof.
  intros Hleft Hright. unfold LrListRel.
  have Htail := lr_append_related T [:: x] rightR
    (ImportedListLast.List_cons T x (ImportedListLast.List_nil T)) rightL
    (@Lean.eq_refl _ _) Hright.
  have Hall := lr_append_related T leftR ([:: x] ++ rightR)
    leftL
    (lr_target_append
      (ImportedListLast.List_cons T x (ImportedListLast.List_nil T)) rightL)
    Hleft Htail.
  exact (sub_imported_eq_trans _ _ _ Hall
    (lr_target_append_assoc T leftL
      (ImportedListLast.List_cons T x (ImportedListLast.List_nil T))
      rightL)).
Qed.

Lemma lr_in_cat_conclusion_correspondence (T : Type) (x : T)
    (xsR : seq T) (xsL : ImportedListLast.List T) :
  LrListRel xsR xsL ->
  PropSPropRel
    (exists left right : seq T,
      Logic.eq xsR (left ++ [:: x] ++ right))
    (ImportedListLast.Exists (ImportedListLast.List T) (fun left =>
      ImportedListLast.Exists (ImportedListLast.List T) (fun right =>
        Lean.eq xsL
          (lr_target_append
            (lr_target_append left
              (ImportedListLast.List_cons T x
                (ImportedListLast.List_nil T)))
            right)))).
Proof.
  intro Hxs.
  apply lr_exists_list_correspondence. intros leftR leftL Hleft.
  apply lr_exists_list_correspondence. intros rightR rightL Hright.
  apply lr_list_eq_correspondence.
  - exact Hxs.
  - exact (lr_in_cat_rhs_related T x leftR rightR leftL rightL
      Hleft Hright).
Qed.

Definition lr_target_in_cat_statement : SProp :=
  forall (T : eqType) (x : T) (xs : ImportedListLast.List T),
    lr_target_mem x xs ->
    ImportedListLast.Exists (ImportedListLast.List T) (fun left =>
      ImportedListLast.Exists (ImportedListLast.List T) (fun right =>
        Lean.eq xs
          (lr_target_append
            (lr_target_append left
              (ImportedListLast.List_cons T x
                (ImportedListLast.List_nil T)))
            right))).

Theorem in_cat_statement_certificate :
  PropSPropRel GeneratedListLastSource.statement_in_cat
    lr_target_in_cat_statement.
Proof.
  unfold GeneratedListLastSource.statement_in_cat,
    lr_target_in_cat_statement.
  apply prop_sprop_rel_intro.
  - intros Hsource T x xsL HmemL.
    pose xsR := lr_to_rocq xsL.
    have Hxs : LrListRel xsR xsL := lr_target_roundtrip xsL.
    have HmemR := sprop_to_prop _ _
      (lr_membership_correspondence T x xsR xsL Hxs) HmemL.
    exact (prop_to_sprop _ _
      (lr_in_cat_conclusion_correspondence T x xsR xsL Hxs)
      (Hsource T x xsR HmemR)).
  - intro Htarget. apply strictly_inhabits.
    intros T x xsR HmemR.
    have Hxs : LrListRel xsR (lr_to_imported xsR) :=
      @Lean.eq_refl _ _.
    have HmemL := prop_to_sprop _ _
      (lr_membership_correspondence T x xsR
        (lr_to_imported xsR) Hxs) HmemR.
    exact (sprop_to_prop _ _
      (lr_in_cat_conclusion_correspondence T x xsR
        (lr_to_imported xsR) Hxs)
      (Htarget T x (lr_to_imported xsR) HmemL)).
Qed.

Print Assumptions lr_erase_canonical.
Print Assumptions lr_membership_correspondence.
Print Assumptions rem_in_statement_certificate.
Print Assumptions in_neq_impl_rem_in_statement_certificate.
Print Assumptions filter_size_rem_statement_certificate.
Print Assumptions lr_target_mem_erase_dups_iff.
Print Assumptions in_seq_equiv_undup_statement_certificate.
Print Assumptions lr_list_eq_correspondence.
Print Assumptions lr_option_eq_correspondence.
Print Assumptions seq1_some_statement_certificate.
Print Assumptions lr_append_related.
Print Assumptions lr_exists_list_correspondence.
Print Assumptions seq_elim_last_statement_certificate.
Print Assumptions lr_target_append_assoc.
Print Assumptions in_cat_statement_certificate.
