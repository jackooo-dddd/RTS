From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From LeanImport Require Import Lean.
From FoundationImported Require Import
  ImportedNondecreasing ImportedSubadditivity.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  NatSubCorrespondence NondecreasingBaseAdapter.
From prosa Require Import GeneratedNondecreasingSource.

(** Artifact-local realization of the approved [seq nat <-> List Nat]
    relation.  Unlike the generic same-carrier adapter, this map also applies
    the already certified Rocq-[nat] / imported-Lean-[Nat] isomorphism. *)
Fixpoint nd_nat_list_to_imported (xs : seq nat) :
    ImportedNondecreasing.List_inst1 Lean.Nat :=
  match xs with
  | [::] => ImportedNondecreasing.List_nil_inst1 Lean.Nat
  | x :: tail => ImportedNondecreasing.List_cons_inst1 Lean.Nat
      (sub_nat_to_imported x) (nd_nat_list_to_imported tail)
  end.

Fixpoint nd_nat_list_to_rocq
    (xs : ImportedNondecreasing.List_inst1 Lean.Nat) : seq nat :=
  match xs with
  | ImportedNondecreasing.List_nil_inst1 => [::]
  | ImportedNondecreasing.List_cons_inst1 x tail =>
      sub_nat_to_rocq x :: nd_nat_list_to_rocq tail
  end.

Definition NdNatListRel (xsR : seq nat)
    (xsL : ImportedNondecreasing.List_inst1 Lean.Nat) : SProp :=
  Lean.eq (nd_nat_list_to_imported xsR) xsL.

Definition nd_nat_list_cons_congr (x y : Lean.Nat)
    (xs ys : ImportedNondecreasing.List_inst1 Lean.Nat) :
  Lean.eq x y -> Lean.eq xs ys ->
  Lean.eq (ImportedNondecreasing.List_cons_inst1 Lean.Nat x xs)
    (ImportedNondecreasing.List_cons_inst1 Lean.Nat y ys) :=
  fun Hx Hxs => sub_imported_eq_congr2
    (ImportedNondecreasing.List_cons_inst1 Lean.Nat) x y xs ys Hx Hxs.

Lemma nd_nat_list_source_roundtrip (xs : seq nat) :
  Logic.eq (nd_nat_list_to_rocq (nd_nat_list_to_imported xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn; first reflexivity.
  f_equal.
  - exact (sub_nat_rocq_roundtrip x).
  - exact IH.
Qed.

Lemma nd_nat_list_target_roundtrip
    (xs : ImportedNondecreasing.List_inst1 Lean.Nat) :
  Lean.eq (nd_nat_list_to_imported (nd_nat_list_to_rocq xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (@Lean.eq_refl _
      (ImportedNondecreasing.List_nil_inst1 Lean.Nat)).
  - exact (nd_nat_list_cons_congr _ _ _ _
      (sub_nat_imported_roundtrip x) IH).
Qed.

(** Nat-specialized membership bridge.  The generated generic adapter cannot
    be applied directly because Rocq [nat] and imported Lean [Nat] are related
    carriers rather than the same carrier. *)
Definition nd_nat_mem_transport (x x' : Lean.Nat)
    (xs xs' : ImportedNondecreasing.List_inst1 Lean.Nat) :
  Lean.eq x x' -> Lean.eq xs xs' ->
  ImportedNondecreasing.List_Mem_inst1 Lean.Nat x xs ->
  ImportedNondecreasing.List_Mem_inst1 Lean.Nat x' xs' :=
  fun Hx Hxs Hmem =>
    match Hx in Lean.eq _ y return
      Lean.eq xs xs' -> ImportedNondecreasing.List_Mem_inst1 Lean.Nat x xs ->
      ImportedNondecreasing.List_Mem_inst1 Lean.Nat y xs'
    with
    | Lean.eq_refl => fun Hlists Hm =>
        match Hlists in Lean.eq _ ys return
          ImportedNondecreasing.List_Mem_inst1 Lean.Nat x xs ->
          ImportedNondecreasing.List_Mem_inst1 Lean.Nat x ys
        with
        | Lean.eq_refl => fun Hm' => Hm'
        end Hm
    end Hxs Hmem.

Definition nd_nat_mem_head_of_rocq_eq (x y : nat)
    (xs : ImportedNondecreasing.List_inst1 Lean.Nat) :
  Logic.eq x y ->
  ImportedNondecreasing.List_Mem_inst1 Lean.Nat (sub_nat_to_imported x)
    (ImportedNondecreasing.List_cons_inst1 Lean.Nat
      (sub_nat_to_imported y) xs) :=
  fun H => match H in Logic.eq _ z return
      ImportedNondecreasing.List_Mem_inst1 Lean.Nat (sub_nat_to_imported x)
        (ImportedNondecreasing.List_cons_inst1 Lean.Nat
          (sub_nat_to_imported z) xs)
    with
    | Logic.eq_refl => ImportedNondecreasing.List_Mem_head_inst1 Lean.Nat
        (sub_nat_to_imported x) xs
    end.

Fixpoint nd_nat_seq_mem_forward (x : nat) (xs : seq nat) :
  SubNatTruth (x \in xs) ->
  ImportedNondecreasing.List_Mem_inst1 Lean.Nat (sub_nat_to_imported x)
    (nd_nat_list_to_imported xs) :=
  match xs as zs return SubNatTruth (x \in zs) ->
      ImportedNondecreasing.List_Mem_inst1 Lean.Nat (sub_nat_to_imported x)
        (nd_nat_list_to_imported zs)
  with
  | [::] => sub_nat_false_elim _
  | y :: ys =>
      match @eqnP x y as r in reflect _ b return
        SubNatTruth (b || (x \in ys)) ->
        ImportedNondecreasing.List_Mem_inst1 Lean.Nat (sub_nat_to_imported x)
          (ImportedNondecreasing.List_cons_inst1 Lean.Nat
            (sub_nat_to_imported y) (nd_nat_list_to_imported ys))
      with
      | ReflectT Hxy => fun _ => nd_nat_mem_head_of_rocq_eq x y _ Hxy
      | ReflectF _ => fun H => ImportedNondecreasing.List_Mem_tail_inst1 Lean.Nat
          (sub_nat_to_imported x) (sub_nat_to_imported y) _
          (nd_nat_seq_mem_forward x ys H)
      end
  end.

Fixpoint nd_nat_imported_mem_decoded (x : Lean.Nat)
    (xs : ImportedNondecreasing.List_inst1 Lean.Nat)
    (H : ImportedNondecreasing.List_Mem_inst1 Lean.Nat x xs) :
  SubNatTruth (sub_nat_to_rocq x \in nd_nat_list_to_rocq xs) :=
  match H with
  | ImportedNondecreasing.List_Mem_head_inst1 ys =>
      nd_mem_head_truth _ _
        (nd_eq_refl_truth Datatypes_nat__canonical__eqtype_Equality
          (sub_nat_to_rocq x))
  | ImportedNondecreasing.List_Mem_tail_inst1 y ys Htail =>
      nd_mem_tail_truth _ _ (nd_nat_imported_mem_decoded x ys Htail)
  end.

Definition nd_nat_mem_truth_transport (x x' : nat)
    (xs xs' : seq nat) : Logic.eq x x' -> Logic.eq xs xs' ->
  SubNatTruth (x \in xs) -> SubNatTruth (x' \in xs') :=
  fun Hx Hxs Htruth =>
    match Hx in Logic.eq _ y return Logic.eq xs xs' ->
      SubNatTruth (x \in xs) -> SubNatTruth (y \in xs')
    with
    | Logic.eq_refl => fun Hlists Ht =>
        match Hlists in Logic.eq _ ys return
          SubNatTruth (x \in xs) -> SubNatTruth (x \in ys)
        with
        | Logic.eq_refl => fun Ht' => Ht'
        end Ht
    end Hxs Htruth.

Definition nd_target_nat_mem (x : Lean.Nat)
    (xs : ImportedNondecreasing.List_inst1 Lean.Nat) : SProp :=
  ImportedNondecreasing.Membership_mem_inst3 Lean.Nat
    (ImportedNondecreasing.List_inst1 Lean.Nat)
    (ImportedNondecreasing.List_instMembership_inst1 Lean.Nat) xs x.

Lemma nd_nat_membership_correspondence xR xL xsR xsL :
  SubNatRel xR xL -> NdNatListRel xsR xsL ->
  PropSPropRel (xR \in xsR) (nd_target_nat_mem xL xsL).
Proof.
  intros Hx Hxs. apply prop_sprop_rel_intro; unfold nd_target_nat_mem.
  - intro Hmem.
    apply (nd_nat_mem_transport _ _ _ _ Hx Hxs).
    apply nd_nat_seq_mem_forward. exact (sub_nat_prop_to_truth _ Hmem).
  - intro Hmem. apply sub_nat_truth_to_strict_prop.
    apply (nd_nat_mem_truth_transport _ _ _ _
      (sub_nat_rocq_roundtrip xR) (nd_nat_list_source_roundtrip xsR)).
    apply nd_nat_imported_mem_decoded.
    exact (nd_nat_mem_transport _ _ _ _
      (sub_imported_eq_sym _ _ Hx) (sub_imported_eq_sym _ _ Hxs) Hmem).
Qed.

Definition nd_target_length
    (xs : ImportedNondecreasing.List_inst1 Lean.Nat) : Lean.Nat :=
  ImportedNondecreasing.List_length_inst1 Lean.Nat xs.

Definition nd_target_nthD
    (xs : ImportedNondecreasing.List_inst1 Lean.Nat)
    (n : Lean.Nat) : Lean.Nat :=
  ImportedNondecreasing.Prosa_Validation_NondecreasingInterface_nthD xs n.

Definition nd_target_le (a b : Lean.Nat) : SProp :=
  ImportedNondecreasing.LE_le_inst1 Lean.Nat
    ImportedNondecreasing.instLENat a b.

Definition nd_target_lt (a b : Lean.Nat) : SProp :=
  ImportedNondecreasing.LT_lt_inst1 Lean.Nat
    ImportedNondecreasing.instLTNat a b.

Lemma nd_le_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (leq aR bR)) (nd_target_le aL bL).
Proof. exact (sub_nat_le_correspondence aR aL bR bL). Qed.

Lemma nd_lt_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (ltn aR bR)) (nd_target_lt aL bL).
Proof. exact (sub_nat_lt_correspondence aR aL bR bL). Qed.

Lemma nd_length_canonical (xs : seq nat) :
  SubNatRel (size xs) (nd_target_length (nd_nat_list_to_imported xs)).
Proof.
  induction xs as [|x xs IH].
  - exact (@Lean.eq_refl Lean.Nat Lean.Nat_zero).
  - cbn [nd_target_length nd_nat_list_to_imported].
    exact (sub_imported_eq_congr Lean.Nat_succ _ _ IH).
Qed.

Lemma nd_length_related xsR xsL : NdNatListRel xsR xsL ->
  SubNatRel (size xsR) (nd_target_length xsL).
Proof.
  intro Hxs. exact (sub_imported_eq_trans _ _ _
    (nd_length_canonical xsR)
    (sub_imported_eq_congr nd_target_length _ _ Hxs)).
Qed.

Lemma nd_nthD_canonical (xs : seq nat) (n : nat) :
  SubNatRel (nth O xs n)
    (nd_target_nthD (nd_nat_list_to_imported xs)
      (sub_nat_to_imported n)).
Proof.
  revert n. induction xs as [|x xs IH]; intro n; destruct n;
    cbn [nd_target_nthD nd_nat_list_to_imported sub_nat_to_imported];
    try exact (@Lean.eq_refl Lean.Nat Lean.Nat_zero);
    try exact (@Lean.eq_refl Lean.Nat (sub_nat_to_imported x));
    exact (IH n).
Qed.

Lemma nd_nthD_related xsR xsL nR nL :
  NdNatListRel xsR xsL -> SubNatRel nR nL ->
  SubNatRel (nth O xsR nR) (nd_target_nthD xsL nL).
Proof.
  intros Hxs Hn. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (nd_nthD_canonical xsR nR)
    (sub_imported_eq_congr2 nd_target_nthD _ _ _ _ Hxs Hn)).
Qed.

Definition nd_target_first0
    (xs : ImportedNondecreasing.List_inst1 Lean.Nat) : Lean.Nat :=
  ImportedNondecreasing.Prosa_Util_List_first0 xs.

Lemma nd_first0_canonical (xs : seq nat) :
  SubNatRel (head O xs) (nd_target_first0 (nd_nat_list_to_imported xs)).
Proof.
  destruct xs as [|x xs]; exact (@Lean.eq_refl Lean.Nat _).
Qed.

Lemma nd_first0_related xsR xsL : NdNatListRel xsR xsL ->
  SubNatRel (head O xsR) (nd_target_first0 xsL).
Proof.
  intro Hxs. exact (sub_imported_eq_trans _ _ _
    (nd_first0_canonical xsR)
    (sub_imported_eq_congr nd_target_first0 _ _ Hxs)).
Qed.

Definition nd_target_last0
    (xs : ImportedNondecreasing.List_inst1 Lean.Nat) : Lean.Nat :=
  ImportedNondecreasing.Prosa_Util_List_last0 xs.

Lemma nd_last0_canonical (xs : seq nat) :
  SubNatRel (last O xs) (nd_target_last0 (nd_nat_list_to_imported xs)).
Proof.
  induction xs as [|x xs IH].
  - exact (@Lean.eq_refl Lean.Nat Lean.Nat_zero).
  - destruct xs as [|y ys].
    + exact (@Lean.eq_refl Lean.Nat (sub_nat_to_imported x)).
    + cbn [last nd_target_last0 nd_nat_list_to_imported] in IH |- *.
      exact IH.
Qed.

Lemma nd_last0_related xsR xsL : NdNatListRel xsR xsL ->
  SubNatRel (last O xsR) (nd_target_last0 xsL).
Proof.
  intro Hxs. exact (sub_imported_eq_trans _ _ _
    (nd_last0_canonical xsR)
    (sub_imported_eq_congr nd_target_last0 _ _ Hxs)).
Qed.

Definition nd_target_append
    (xs ys : ImportedNondecreasing.List_inst1 Lean.Nat) :
    ImportedNondecreasing.List_inst1 Lean.Nat :=
  ImportedNondecreasing.HAppend_hAppend_inst7
    (ImportedNondecreasing.List_inst1 Lean.Nat)
    (ImportedNondecreasing.List_inst1 Lean.Nat)
    (ImportedNondecreasing.List_inst1 Lean.Nat)
    (ImportedNondecreasing.instHAppendOfAppend_inst1
      (ImportedNondecreasing.List_inst1 Lean.Nat)
      (ImportedNondecreasing.List_instAppend_inst1 Lean.Nat)) xs ys.

Lemma nd_append_canonical (xs ys : seq nat) :
  NdNatListRel (xs ++ ys)
    (nd_target_append (nd_nat_list_to_imported xs)
      (nd_nat_list_to_imported ys)).
Proof.
  induction xs as [|x xs IH].
  - exact (@Lean.eq_refl _ (nd_nat_list_to_imported ys)).
  - cbn [cat nd_target_append nd_nat_list_to_imported].
    exact (nd_nat_list_cons_congr _ _ _ _
      (@Lean.eq_refl Lean.Nat (sub_nat_to_imported x)) IH).
Qed.

Lemma nd_append_related xsR xsL ysR ysL :
  NdNatListRel xsR xsL -> NdNatListRel ysR ysL ->
  NdNatListRel (xsR ++ ysR) (nd_target_append xsL ysL).
Proof.
  intros Hxs Hys. unfold NdNatListRel.
  exact (sub_imported_eq_trans _ _ _ (nd_append_canonical xsR ysR)
    (sub_imported_eq_congr2 nd_target_append _ _ _ _ Hxs Hys)).
Qed.

Definition nd_target_max (a b : Lean.Nat) : Lean.Nat :=
  ImportedNondecreasing.Nat_max a b.

Definition nd_imported_false_to_strict
    (H : ImportedNondecreasing.False) : StrictlyInhabited Logic.False :=
  match H with end.

Lemma nd_max_canonical (a b : nat) :
  Lean.eq (nd_target_max (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (maxn a b)).
Proof.
  unfold nd_target_max, ImportedNondecreasing.Nat_max,
    ImportedNondecreasing.Max_max_inst1, ImportedNondecreasing.Nat_instMax,
    ImportedNondecreasing.maxOfLe_inst1.
  cbn.
  destruct (ImportedNondecreasing.Nat_decLe
    (sub_nat_to_imported a) (sub_nat_to_imported b)) as [Hnle|Hle].
  - have Hrel := sub_nat_le_correspondence a (sub_nat_to_imported a)
      b (sub_nat_to_imported b) (sub_nat_rel_canonical a)
      (sub_nat_rel_canonical b).
    have Hnot : ~ is_true (leq a b).
    { intro Hab. exact (interpret_strict Logic.False
        (nd_imported_false_to_strict (Hnle (prop_to_sprop _ _ Hrel Hab)))). }
    have Hba : is_true (leq b a).
    { move: (leq_total a b) => /orP [Hab|Hba]; last exact Hba.
      exfalso. exact (Hnot Hab). }
    have Hmax : maxn a b = a := (elimT maxn_idPl Hba).
    rewrite Hmax. exact (@Lean.eq_refl Lean.Nat (sub_nat_to_imported a)).
  - have Hab : is_true (leq a b).
    { have Hrel := sub_nat_le_correspondence a (sub_nat_to_imported a)
        b (sub_nat_to_imported b) (sub_nat_rel_canonical a)
        (sub_nat_rel_canonical b).
      exact (sprop_to_prop _ _ Hrel Hle). }
    have Hmax : maxn a b = b := (elimT maxn_idPr Hab).
    rewrite Hmax. exact (@Lean.eq_refl Lean.Nat (sub_nat_to_imported b)).
Qed.

Lemma nd_foldl_max_canonical (z : nat) (xs : seq nat) :
  Lean.eq
    (ImportedNondecreasing.List_foldl_inst3 Lean.Nat Lean.Nat
      ImportedNondecreasing.Nat_max (sub_nat_to_imported z)
      (nd_nat_list_to_imported xs))
    (sub_nat_to_imported (foldl maxn z xs)).
Proof.
  revert z. induction xs as [|x xs IH]; intro z.
  - exact (@Lean.eq_refl Lean.Nat (sub_nat_to_imported z)).
  - cbn [nd_nat_list_to_imported foldl].
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_congr
        (fun init => ImportedNondecreasing.List_foldl_inst3
          Lean.Nat Lean.Nat ImportedNondecreasing.Nat_max init
          (nd_nat_list_to_imported xs)) _ _ (nd_max_canonical z x))
      (IH (maxn z x))).
Qed.

Definition nd_target_max0
    (xs : ImportedNondecreasing.List_inst1 Lean.Nat) : Lean.Nat :=
  ImportedNondecreasing.Prosa_Util_List_max0 xs.

Lemma nd_max0_canonical (xs : seq nat) :
  SubNatRel (foldl maxn O xs)
    (nd_target_max0 (nd_nat_list_to_imported xs)).
Proof.
  exact (sub_imported_eq_sym _ _ (nd_foldl_max_canonical O xs)).
Qed.

Lemma nd_max0_related xsR xsL : NdNatListRel xsR xsL ->
  SubNatRel (foldl maxn O xsR) (nd_target_max0 xsL).
Proof.
  intro Hxs. exact (sub_imported_eq_trans _ _ _ (nd_max0_canonical xsR)
    (sub_imported_eq_congr nd_target_max0 _ _ Hxs)).
Qed.

(** The target namespace has its own imported spelling of Lean's truncated
    subtraction.  The computational proof is an artifact-local adapter over
    the already certified Rocq iterated-predecessor characterization. *)
Definition nd_target_sub (a b : Lean.Nat) : Lean.Nat :=
  ImportedNondecreasing.Nat_sub a b.

Lemma nd_target_sub_zero (a : Lean.Nat) :
  Lean.eq (nd_target_sub a Lean.Nat_zero) a.
Proof. exact (@Lean.eq_refl Lean.Nat a). Qed.

Lemma nd_target_sub_succ (a b : Lean.Nat) :
  Lean.eq (nd_target_sub a (Lean.Nat_succ b))
    (ImportedNondecreasing.Nat_pred (nd_target_sub a b)).
Proof.
  exact (@Lean.eq_refl Lean.Nat
    (ImportedNondecreasing.Nat_pred (nd_target_sub a b))).
Qed.

Definition nd_target_pred_canonical (n : nat) :
  Lean.eq (ImportedNondecreasing.Nat_pred (sub_nat_to_imported n))
    (sub_nat_to_imported (Nat.pred n)) :=
  match n return
    Lean.eq (ImportedNondecreasing.Nat_pred (sub_nat_to_imported n))
      (sub_nat_to_imported (Nat.pred n))
  with
  | O => @Lean.eq_refl Lean.Nat Lean.Nat_zero
  | S n' => @Lean.eq_refl Lean.Nat (sub_nat_to_imported n')
  end.

Lemma nd_target_sub_iterated_pred (a b : nat) :
  Lean.eq
    (nd_target_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (rocq_iterated_pred a b)).
Proof.
  induction b as [|b IH].
  - exact (nd_target_sub_zero (sub_nat_to_imported a)).
  - exact (sub_imported_eq_trans _ _ _
      (nd_target_sub_succ _ _)
      (sub_imported_eq_trans _ _ _
        (sub_imported_eq_congr ImportedNondecreasing.Nat_pred _ _ IH)
        (nd_target_pred_canonical (rocq_iterated_pred a b)))).
Qed.

Lemma nd_target_sub_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR - bR) (nd_target_sub aL bL).
Proof.
  intros Ha Hb. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _
      (sub_imported_eq_trans _ _ _
        (nd_target_sub_iterated_pred aR bR)
        (coq_eq_to_imported_eq _ _
          (f_equal sub_nat_to_imported
            (rocq_iterated_pred_is_subn aR bR)))))
    (sub_imported_eq_congr2 nd_target_sub _ _ _ _ Ha Hb)).
Qed.

Definition nd_target_hsub (a b : Lean.Nat) : Lean.Nat :=
  ImportedNondecreasing.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedNondecreasing.instHSub_inst1 Lean.Nat
      ImportedNondecreasing.instSubNat) a b.

Lemma nd_target_hsub_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR - bR) (nd_target_hsub aL bL).
Proof. exact (nd_target_sub_correspondence aR aL bR bL). Qed.

(** Reusable predicate/filter interface for the actual imported artifact. *)
Definition NdNatPredRel (PR : nat -> bool)
    (PL : Lean.Nat -> ImportedNondecreasing.Bool) : SProp :=
  forall nR nL, SubNatRel nR nL -> NdBoolRel (PR nR) (PL nL).

Definition nd_nat_pred_from_imported
    (PL : Lean.Nat -> ImportedNondecreasing.Bool) : nat -> bool :=
  fun n => nd_bool_to_rocq (PL (sub_nat_to_imported n)).

Definition nd_nat_pred_to_imported (PR : nat -> bool) :
    Lean.Nat -> ImportedNondecreasing.Bool :=
  fun n => nd_bool_to_imported (PR (sub_nat_to_rocq n)).

Lemma nd_nat_pred_rel_surjective
    (PL : Lean.Nat -> ImportedNondecreasing.Bool) :
  NdNatPredRel (nd_nat_pred_from_imported PL) PL.
Proof.
  intros nR nL Hn. unfold NdBoolRel, nd_nat_pred_from_imported.
  exact (sub_imported_eq_trans _ _ _
    (nd_bool_target_roundtrip (PL (sub_nat_to_imported nR)))
    (sub_imported_eq_congr PL _ _ Hn)).
Qed.

Lemma nd_nat_pred_rel_canonical (PR : nat -> bool) :
  NdNatPredRel PR (nd_nat_pred_to_imported PR).
Proof.
  intros nR nL Hn. unfold NdBoolRel, nd_nat_pred_to_imported.
  have Hback : Logic.eq (sub_nat_to_rocq nL) nR.
  { have Hdecoded :=
      f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ Hn).
    rewrite (sub_nat_rocq_roundtrip nR) in Hdecoded.
    exact (Logic.eq_sym Hdecoded). }
  rewrite Hback. exact (@Lean.eq_refl _ _).
Qed.

Definition nd_target_filter (P : Lean.Nat -> ImportedNondecreasing.Bool)
    (xs : ImportedNondecreasing.List_inst1 Lean.Nat) :
    ImportedNondecreasing.List_inst1 Lean.Nat :=
  ImportedNondecreasing.List_filter_inst1 Lean.Nat P xs.

Definition nd_target_filter_match (b : ImportedNondecreasing.Bool)
    (x : Lean.Nat) (tail : ImportedNondecreasing.List_inst1 Lean.Nat) :=
  ImportedNondecreasing.Prosa_Validation_NondecreasingInterface_production_filter_cons_match_1
    (fun _ : ImportedNondecreasing.Bool =>
      ImportedNondecreasing.List_inst1 Lean.Nat) b
    (fun _ : ImportedNondecreasing.Unit =>
      ImportedNondecreasing.List_cons_inst1 Lean.Nat x tail)
    (fun _ : ImportedNondecreasing.Unit => tail).

Lemma nd_target_filter_match_canonical (b : bool) (x : Lean.Nat)
    (tail : ImportedNondecreasing.List_inst1 Lean.Nat) :
  Lean.eq (nd_target_filter_match (nd_bool_to_imported b) x tail)
    (match b with
     | true => ImportedNondecreasing.List_cons_inst1 Lean.Nat x tail
     | false => tail
     end).
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Lemma nd_filter_branch_canonical (b : bool) (x : nat)
    (filtered : seq nat)
    (tail : ImportedNondecreasing.List_inst1 Lean.Nat) :
  Lean.eq tail (nd_nat_list_to_imported filtered) ->
  Lean.eq
    (match b with
     | true => ImportedNondecreasing.List_cons_inst1 Lean.Nat
         (sub_nat_to_imported x) tail
     | false => tail
     end)
    (nd_nat_list_to_imported
      (match b with true => x :: filtered | false => filtered end)).
Proof.
  intro IH. destruct b; cbn.
  - exact (sub_imported_eq_congr
      (ImportedNondecreasing.List_cons_inst1 Lean.Nat
        (sub_nat_to_imported x)) _ _ IH).
  - exact IH.
Qed.

Lemma nd_source_filter_cons (P : nat -> bool) (x : nat) (xs : seq nat) :
  Logic.eq
    (match P x with
     | true => x :: [seq y <- xs | P y]
     | false => [seq y <- xs | P y]
     end)
    [seq y <- x :: xs | P y].
Proof. cbn. destruct (P x); reflexivity. Qed.

Lemma nd_filter_with_pred_canonical PR PL : NdNatPredRel PR PL ->
  forall xs : seq nat,
  Lean.eq (nd_target_filter PL (nd_nat_list_to_imported xs))
    (nd_nat_list_to_imported [seq x <- xs | PR x]).
Proof.
  intro HP. induction xs as [|x xs IH].
  - exact
      (ImportedNondecreasing.Prosa_Validation_NondecreasingInterface_production_filter_nil
        PL).
  - refine (sub_imported_eq_trans _ _ _
      (ImportedNondecreasing.Prosa_Validation_NondecreasingInterface_production_filter_cons
        PL (sub_nat_to_imported x) (nd_nat_list_to_imported xs)) _).
    have Hb := HP x (sub_nat_to_imported x) (sub_nat_rel_canonical x).
    refine (sub_imported_eq_trans _ _ _
      (sub_imported_eq_congr
        (fun b => nd_target_filter_match b (sub_nat_to_imported x)
          (nd_target_filter PL (nd_nat_list_to_imported xs))) _ _
        (sub_imported_eq_sym _ _ Hb)) _).
    refine (sub_imported_eq_trans _ _ _
      (nd_target_filter_match_canonical (PR x) (sub_nat_to_imported x)
        (nd_target_filter PL (nd_nat_list_to_imported xs))) _).
    refine (sub_imported_eq_trans _ _ _
      (nd_filter_branch_canonical (PR x) x [seq y <- xs | PR y]
        (nd_target_filter PL (nd_nat_list_to_imported xs)) IH) _).
    exact (coq_eq_to_imported_eq _ _
      (f_equal nd_nat_list_to_imported (nd_source_filter_cons PR x xs))).
Qed.

Lemma nd_filter_related PR PL xsR xsL :
  NdNatPredRel PR PL -> NdNatListRel xsR xsL ->
  NdNatListRel [seq x <- xsR | PR x] (nd_target_filter PL xsL).
Proof.
  intros HP Hxs. unfold NdNatListRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (nd_filter_with_pred_canonical PR PL HP xsR))
    (sub_imported_eq_congr (nd_target_filter PL) _ _ Hxs)).
Qed.

Definition nd_bool_false_elim (H : is_true false) : Logic.False.
Proof. discriminate H. Defined.

Definition nd_target_false_elim (Q : SProp)
    (H : ImportedNondecreasing.False) : Q := match H return Q with end.

Lemma nd_decide_bool_correspondence (b : bool) (Q : SProp)
    (d : ImportedNondecreasing.Decidable Q) :
  PropSPropRel (is_true b) Q ->
  NdBoolRel b (ImportedNondecreasing.Decidable_decide Q d).
Proof.
  intro Hrel. unfold NdBoolRel.
  destruct d as [Hfalse | Htrue]; destruct b; cbn.
  - exact (nd_target_false_elim _
      (Hfalse (prop_to_sprop _ _ Hrel (Logic.eq_refl true)))).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - exact (nd_target_false_elim _ (nd_coq_false_to_target
      (nd_bool_false_elim (sprop_to_prop _ _ Hrel Htrue)))).
Qed.

Definition nd_target_nat_mem_decidable (x : Lean.Nat)
    (xs : ImportedNondecreasing.List_inst1 Lean.Nat) :
    ImportedNondecreasing.Decidable (nd_target_nat_mem x xs) :=
  ImportedNondecreasing.List_instDecidableMemOfLawfulBEq_inst1 Lean.Nat
    (ImportedNondecreasing.instBEqOfDecidableEq_inst1 Lean.Nat
      ImportedNondecreasing.instDecidableEqNat)
    ImportedNondecreasing.Nat_instLawfulBEq x xs.

Definition nd_target_decide_mem (x : Lean.Nat)
    (xs : ImportedNondecreasing.List_inst1 Lean.Nat) :
    ImportedNondecreasing.Bool :=
  ImportedNondecreasing.Decidable_decide (nd_target_nat_mem x xs)
    (nd_target_nat_mem_decidable x xs).

Lemma nd_decide_mem_related xR xL xsR xsL :
  SubNatRel xR xL -> NdNatListRel xsR xsL ->
  NdBoolRel (xR \in xsR) (nd_target_decide_mem xL xsL).
Proof.
  intros Hx Hxs. apply nd_decide_bool_correspondence.
  exact (nd_nat_membership_correspondence _ _ _ _ Hx Hxs).
Qed.

Definition nd_target_positive (x : Lean.Nat) : ImportedNondecreasing.Bool :=
  ImportedNondecreasing.Decidable_decide (nd_target_lt Lean.Nat_zero x)
    (ImportedNondecreasing.Nat_decLt Lean.Nat_zero x).

Lemma nd_positive_pred_related (xR : nat) (xL : Lean.Nat) :
  SubNatRel xR xL ->
  NdBoolRel (ltn O xR) (nd_target_positive xL).
Proof.
  intro Hx. apply nd_decide_bool_correspondence.
  exact (nd_lt_correspondence O Lean.Nat_zero xR xL
    (sub_nat_rel_canonical O) Hx).
Qed.

(** Half-open interval enumeration used by [index_iota]. *)
Definition nd_op_target_one : Lean.Nat := Lean.Nat_succ Lean.Nat_zero.

Definition nd_op_target_add (a b : Lean.Nat) : Lean.Nat :=
  ImportedNondecreasing.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedNondecreasing.instHAdd_inst1 Lean.Nat
      ImportedNondecreasing.instAddNat) a b.

Lemma nd_op_add_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR + bR) (nd_op_target_add aL bL).
Proof. exact (sub_add_correspondence aR aL bR bL). Qed.

Lemma nd_op_succ_correspondence nR nL : SubNatRel nR nL ->
  SubNatRel nR.+1 (nd_op_target_add nL nd_op_target_one).
Proof.
  intro Hn. rewrite -addn1.
  exact (nd_op_add_correspondence _ _ 1 nd_op_target_one Hn
    (sub_nat_rel_canonical 1)).
Qed.

Definition nd_target_range_prime (start len : Lean.Nat) :
    ImportedNondecreasing.List_inst1 Lean.Nat :=
  ImportedNondecreasing.List_range' start len nd_op_target_one.

Definition nd_target_index_iota (a b : Lean.Nat) :
    ImportedNondecreasing.List_inst1 Lean.Nat :=
  ImportedNondecreasing.Prosa_Util_List_index_iota a b.

Lemma nd_iota_canonical (m n : nat) :
  NdNatListRel (iota m n)
    (nd_target_range_prime (sub_nat_to_imported m)
      (sub_nat_to_imported n)).
Proof.
  revert m. induction n as [|n IH]; intro m.
  - cbn [iota nd_nat_list_to_imported].
    exact (sub_imported_eq_sym _ _
      (ImportedNondecreasing.Prosa_Validation_NondecreasingInterface_production_range_prime_zero
        (sub_nat_to_imported m))).
  - cbn [iota nd_nat_list_to_imported].
    refine (sub_imported_eq_trans _ _ _
      (nd_nat_list_cons_congr _ _ _ _
        (@Lean.eq_refl Lean.Nat (sub_nat_to_imported m)) (IH m.+1)) _).
    exact (sub_imported_eq_sym _ _
      (ImportedNondecreasing.Prosa_Validation_NondecreasingInterface_production_range_prime_succ
        (sub_nat_to_imported m) (sub_nat_to_imported n))).
Qed.

Lemma nd_iota_related mR mL nR nL :
  SubNatRel mR mL -> SubNatRel nR nL ->
  NdNatListRel (iota mR nR) (nd_target_range_prime mL nL).
Proof.
  intros Hm Hn. unfold NdNatListRel.
  exact (sub_imported_eq_trans _ _ _ (nd_iota_canonical mR nR)
    (sub_imported_eq_congr2 nd_target_range_prime _ _ _ _ Hm Hn)).
Qed.

Lemma nd_index_iota_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  NdNatListRel (index_iota aR bR) (nd_target_index_iota aL bL).
Proof.
  intros Ha Hb. rewrite /index_iota.
  have Hsub := nd_target_hsub_correspondence bR bL aR aL Hb Ha.
  have Hiota := nd_iota_related aR aL (bR - aR)
    (nd_target_hsub bL aL) Ha Hsub.
  unfold NdNatListRel in Hiota |- *.
  exact (sub_imported_eq_trans _ _ _ Hiota
    (sub_imported_eq_sym _ _
      (ImportedNondecreasing.Prosa_Validation_NondecreasingInterface_production_index_iota_eq
        aL bL))).
Qed.

(** Ordered duplicate-removal correspondence.  Unlike the older extensional
    membership-only bridge, these lemmas preserve the exact list produced by
    MathComp [undup] and the actual compiled Lean [List.dedup]. *)
Definition nd_target_dedup_nat
    (xs : ImportedNondecreasing.List_inst1 Lean.Nat) :
    ImportedNondecreasing.List_inst1 Lean.Nat :=
  ImportedNondecreasing.List_dedup_inst1 Lean.Nat
    ImportedNondecreasing.instDecidableEqNat xs.

Lemma nd_bool_eq_false_elim (b : bool) : Logic.eq b false ->
  is_true b -> Logic.False.
Proof. destruct b; discriminate. Qed.

Lemma nd_target_ite_true {A : Type} (P : SProp)
    (d : ImportedNondecreasing.Decidable P) (t e : A) :
  P -> Lean.eq (ImportedNondecreasing.ite A P d t e) t.
Proof.
  intro HP. destruct d as [Hnot | Hyes]; cbn.
  - exact (nd_target_false_elim _ (Hnot HP)).
  - exact (@Lean.eq_refl _ _).
Qed.

Lemma nd_target_ite_false {A : Type} (P : SProp)
    (d : ImportedNondecreasing.Decidable P) (t e : A) :
  ImportedNondecreasing.Not P ->
  Lean.eq (ImportedNondecreasing.ite A P d t e) e.
Proof.
  intro Hnot. destruct d as [Hno | HP]; cbn.
  - exact (@Lean.eq_refl _ _).
  - exact (nd_target_false_elim _ (Hnot HP)).
Qed.

Lemma nd_undup_nat_canonical (xs : seq nat) :
  NdNatListRel (undup xs) (nd_target_dedup_nat (nd_nat_list_to_imported xs)).
Proof.
  induction xs as [|x xs IH].
  - unfold NdNatListRel, nd_target_dedup_nat. cbn [undup].
    exact (sub_imported_eq_sym _ _
      ImportedNondecreasing.Prosa_Validation_NondecreasingInterface_production_dedup_nil).
  - unfold NdNatListRel, nd_target_dedup_nat in IH |- *.
    cbn [undup nd_nat_list_to_imported].
    refine (sub_imported_eq_trans _ _ _ _
      (sub_imported_eq_sym _ _
        (ImportedNondecreasing.Prosa_Validation_NondecreasingInterface_production_dedup_cons
          (sub_nat_to_imported x) (nd_nat_list_to_imported xs)))).
    destruct (x \in xs) eqn:HmemR.
    + try rewrite HmemR. cbn.
      refine (sub_imported_eq_trans _ _ _ IH
        (sub_imported_eq_sym _ _ (nd_target_ite_true _ _ _ _ _))).
      exact (prop_to_sprop _ _
        (nd_nat_membership_correspondence x (sub_nat_to_imported x)
          xs (nd_nat_list_to_imported xs) (sub_nat_rel_canonical x)
          (@Lean.eq_refl _ _)) HmemR).
    + try rewrite HmemR. cbn.
      refine (sub_imported_eq_trans _ _ _
        (nd_nat_list_cons_congr _ _ _ _ (@Lean.eq_refl _ _) IH)
        (sub_imported_eq_sym _ _ (nd_target_ite_false _ _ _ _ _))).
      intro HmemL. apply nd_coq_false_to_target.
      exact (nd_bool_eq_false_elim _ HmemR
        (sprop_to_prop _ _
          (nd_nat_membership_correspondence x (sub_nat_to_imported x)
            xs (nd_nat_list_to_imported xs) (sub_nat_rel_canonical x)
            (@Lean.eq_refl _ _)) HmemL)).
Qed.

Lemma nd_undup_nat_related xsR xsL : NdNatListRel xsR xsL ->
  NdNatListRel (undup xsR) (nd_target_dedup_nat xsL).
Proof.
  intro Hxs. unfold NdNatListRel.
  exact (sub_imported_eq_trans _ _ _ (nd_undup_nat_canonical xsR)
    (sub_imported_eq_congr nd_target_dedup_nat _ _ Hxs)).
Qed.

Fixpoint nd_list1_to_imported {T : Type} (xs : seq T) :
    ImportedNondecreasing.List_inst1 T :=
  match xs with
  | [::] => ImportedNondecreasing.List_nil_inst1 T
  | x :: tail => ImportedNondecreasing.List_cons_inst1 T x
      (nd_list1_to_imported tail)
  end.

Fixpoint nd_list1_to_rocq {T : Type}
    (xs : ImportedNondecreasing.List_inst1 T) : seq T :=
  match xs with
  | ImportedNondecreasing.List_nil_inst1 => [::]
  | ImportedNondecreasing.List_cons_inst1 x tail =>
      x :: nd_list1_to_rocq tail
  end.

Definition NdList1Rel {T : Type} (xsR : seq T)
    (xsL : ImportedNondecreasing.List_inst1 T) : SProp :=
  Lean.eq (nd_list1_to_imported xsR) xsL.

Lemma nd_list1_source_roundtrip {T : Type} (xs : seq T) :
  Logic.eq (nd_list1_to_rocq (nd_list1_to_imported xs)) xs.
Proof. induction xs; cbn; first reflexivity. f_equal. exact IHxs. Qed.

Lemma nd_list1_target_roundtrip {T : Type}
    (xs : ImportedNondecreasing.List_inst1 T) :
  Lean.eq (nd_list1_to_imported (nd_list1_to_rocq xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr
      (ImportedNondecreasing.List_cons_inst1 T x) _ _ IH).
Qed.

Definition nd_target_mem1 {T : Type} (x : T)
    (xs : ImportedNondecreasing.List_inst1 T) : SProp :=
  ImportedNondecreasing.Membership_mem_inst3 T
    (ImportedNondecreasing.List_inst1 T)
    (ImportedNondecreasing.List_instMembership_inst1 T) xs x.

Definition nd_list1_mem_transport {T : Type} (x : T)
    (xs ys : ImportedNondecreasing.List_inst1 T) :
  Lean.eq xs ys -> ImportedNondecreasing.List_Mem_inst1 T x xs ->
  ImportedNondecreasing.List_Mem_inst1 T x ys :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ zs return
      ImportedNondecreasing.List_Mem_inst1 T x zs with
    | Lean.eq_refl => Hmem
    end.

Definition nd_mem1_head_of_coq_eq {T : Type} (x y : T)
    (xs : ImportedNondecreasing.List_inst1 T) : Logic.eq x y ->
    ImportedNondecreasing.List_Mem_inst1 T x
      (ImportedNondecreasing.List_cons_inst1 T y xs) :=
  fun H => match H in Logic.eq _ z return
      ImportedNondecreasing.List_Mem_inst1 T x
        (ImportedNondecreasing.List_cons_inst1 T z xs)
    with
    | Logic.eq_refl => ImportedNondecreasing.List_Mem_head_inst1 T x xs
    end.

Fixpoint nd_seq_mem1_forward {T : eqType} (x : T) (xs : seq T) :
    SubNatTruth (x \in xs) ->
    ImportedNondecreasing.List_Mem_inst1 T x (nd_list1_to_imported xs) :=
  match xs as zs return SubNatTruth (x \in zs) ->
      ImportedNondecreasing.List_Mem_inst1 T x
        (nd_list1_to_imported zs) with
  | [::] => sub_nat_false_elim _
  | y :: ys =>
      match @eqP T x y as r in reflect _ b return
        SubNatTruth (b || (x \in ys)) ->
        ImportedNondecreasing.List_Mem_inst1 T x
          (ImportedNondecreasing.List_cons_inst1 T y
            (nd_list1_to_imported ys)) with
      | ReflectT Hxy => fun _ => nd_mem1_head_of_coq_eq x y _ Hxy
      | ReflectF _ => fun H => ImportedNondecreasing.List_Mem_tail_inst1 T
          x y _ (nd_seq_mem1_forward x ys H)
      end
  end.

Fixpoint nd_imported_mem1_decoded {T : eqType} (x : T)
    (xs : ImportedNondecreasing.List_inst1 T)
    (H : ImportedNondecreasing.List_Mem_inst1 T x xs) :
    SubNatTruth (x \in nd_list1_to_rocq xs) :=
  match H with
  | ImportedNondecreasing.List_Mem_head_inst1 ys =>
      nd_mem_head_truth _ _ (nd_eq_refl_truth T x)
  | ImportedNondecreasing.List_Mem_tail_inst1 y ys Htail =>
      nd_mem_tail_truth _ _ (nd_imported_mem1_decoded x ys Htail)
  end.

Lemma nd_membership1_correspondence (T : eqType) (x : T)
    (xsR : seq T) (xsL : ImportedNondecreasing.List_inst1 T) :
  NdList1Rel xsR xsL ->
  PropSPropRel (x \in xsR) (nd_target_mem1 x xsL).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intro Hmem. unfold nd_target_mem1.
    apply (nd_list1_mem_transport x _ _ Hxs).
    apply nd_seq_mem1_forward.
    exact (sub_nat_prop_to_truth _ Hmem).
  - intro Hmem. apply sub_nat_truth_to_strict_prop.
    apply (nd_mem_truth_transport x _ _ (nd_list1_source_roundtrip xsR)).
    apply nd_imported_mem1_decoded.
    unfold nd_target_mem1 in Hmem.
    exact (nd_list1_mem_transport x _ _
      (sub_imported_eq_sym _ _ Hxs) Hmem).
Qed.

Definition nd_target_dedup (T : eqType)
    (xs : ImportedNondecreasing.List_inst1 T) :
    ImportedNondecreasing.List_inst1 T :=
  ImportedNondecreasing.List_dedup_inst1 T (nd_decidable_eq T) xs.

Definition nd_target_mem_decidable (T : eqType) (x : T)
    (xs : ImportedNondecreasing.List_inst1 T) :
    ImportedNondecreasing.Decidable (nd_target_mem1 x xs) :=
  ImportedNondecreasing.List_instDecidableMemOfLawfulBEq_inst1 T
    (ImportedNondecreasing.instBEqOfDecidableEq_inst1 T (nd_decidable_eq T))
    (ImportedNondecreasing.instLawfulBEq_inst1 T (nd_decidable_eq T)) x xs.

Lemma nd_undup_canonical (T : eqType) (xs : seq T) :
  NdList1Rel (undup xs) (nd_target_dedup T (nd_list1_to_imported xs)).
Proof.
  induction xs as [|x xs IH].
  - exact (@Lean.eq_refl _ _).
  - unfold NdList1Rel, nd_target_dedup in IH |- *.
    cbn [undup nd_list1_to_imported].
    refine (sub_imported_eq_trans _ _ _ _
      (sub_imported_eq_sym _ _
        (ImportedNondecreasing.List_dedup_cons_inst1 T (nd_decidable_eq T)
          x (nd_list1_to_imported xs)))).
    destruct (x \in xs) eqn:HmemR.
    + try rewrite HmemR. cbn.
      refine (sub_imported_eq_trans _ _ _ IH
        (sub_imported_eq_sym _ _ (nd_target_ite_true _ _ _ _ _))).
      exact (prop_to_sprop _ _
        (nd_membership1_correspondence T x xs
          (nd_list1_to_imported xs) (@Lean.eq_refl _ _)) HmemR).
    + try rewrite HmemR. cbn.
      refine (sub_imported_eq_trans _ _ _
        (sub_imported_eq_congr
          (ImportedNondecreasing.List_cons_inst1 T x) _ _ IH)
        (sub_imported_eq_sym _ _ (nd_target_ite_false _ _ _ _ _))).
      intro HmemL. apply nd_coq_false_to_target.
      exact (nd_bool_eq_false_elim _ HmemR
        (sprop_to_prop _ _
          (nd_membership1_correspondence T x xs
            (nd_list1_to_imported xs) (@Lean.eq_refl _ _)) HmemL)).
Qed.

Lemma nd_undup_related (T : eqType) xsR xsL : NdList1Rel xsR xsL ->
  NdList1Rel (undup xsR) (nd_target_dedup T xsL).
Proof.
  intro Hxs. unfold NdList1Rel.
  exact (sub_imported_eq_trans _ _ _ (nd_undup_canonical T xsR)
    (sub_imported_eq_congr (nd_target_dedup T) _ _ Hxs)).
Qed.

Lemma nd_source_distances_nil :
  Logic.eq (GeneratedNondecreasingSource.distances [::]) [::].
Proof. reflexivity. Qed.

Lemma nd_source_distances_single (x : nat) :
  Logic.eq (GeneratedNondecreasingSource.distances [:: x]) [::].
Proof. reflexivity. Qed.

Lemma nd_source_distances_cons (x y : nat) (ys : seq nat) :
  Logic.eq (GeneratedNondecreasingSource.distances [:: x, y & ys])
    ((y - x) :: GeneratedNondecreasingSource.distances (y :: ys)).
Proof.
  cbn [GeneratedNondecreasingSource.distances drop zip map].
  rw drop0.
  reflexivity.
Qed.

Lemma nd_distances_canonical (xs : seq nat) :
  NdNatListRel (GeneratedNondecreasingSource.distances xs)
    (ImportedNondecreasing.Prosa_Util_Nondecreasing_distances
      (nd_nat_list_to_imported xs)).
Proof.
  induction xs as [|x xs IH].
  - unfold NdNatListRel. rewrite nd_source_distances_nil.
    exact (sub_imported_eq_sym _ _
      ImportedNondecreasing.Prosa_Validation_NondecreasingInterface_production_distances_nil).
  - destruct xs as [|y ys].
    + unfold NdNatListRel. rewrite nd_source_distances_single.
      exact (sub_imported_eq_sym _ _
        (ImportedNondecreasing.Prosa_Validation_NondecreasingInterface_production_distances_single
          (sub_nat_to_imported x))).
    + unfold NdNatListRel in IH |- *.
      rewrite nd_source_distances_cons. cbn [nd_nat_list_to_imported].
      exact (sub_imported_eq_trans _ _ _
        (nd_nat_list_cons_congr _ _ _ _
          (nd_target_hsub_correspondence y (sub_nat_to_imported y)
            x (sub_nat_to_imported x)
            (sub_nat_rel_canonical y) (sub_nat_rel_canonical x)) IH)
        (sub_imported_eq_sym _ _
          (ImportedNondecreasing.Prosa_Validation_NondecreasingInterface_production_distances_cons
            (sub_nat_to_imported x) (sub_nat_to_imported y)
            (nd_nat_list_to_imported ys)))).
Qed.

Theorem distances_definition_certificate xsR xsL :
  NdNatListRel xsR xsL ->
  NdNatListRel (GeneratedNondecreasingSource.distances xsR)
    (ImportedNondecreasing.Prosa_Util_Nondecreasing_distances xsL).
Proof.
  intro Hxs. unfold NdNatListRel.
  exact (sub_imported_eq_trans _ _ _ (nd_distances_canonical xsR)
    (sub_imported_eq_congr
      ImportedNondecreasing.Prosa_Util_Nondecreasing_distances _ _ Hxs)).
Qed.

(** The two order predicates are proved compositionally from the already
    certified Nat order, list length, and zero-defaulted lookup operations.
    Neither proof uses the source or imported business theorem constants. *)
Theorem nondecreasing_sequence_definition_certificate xsR xsL :
  NdNatListRel xsR xsL ->
  PropSPropRel
    (GeneratedNondecreasingSource.nondecreasing_sequence xsR)
    (ImportedNondecreasing.Prosa_Util_Nondecreasing_nondecreasing_sequence
      xsL).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intros HR n1L n2L HboundsL.
    set n1R := sub_nat_to_rocq n1L.
    set n2R := sub_nat_to_rocq n2L.
    have Hn1 : SubNatRel n1R n1L := sub_nat_rel_surjective n1L.
    have Hn2 : SubNatRel n2R n2L := sub_nat_rel_surjective n2L.
    destruct HboundsL as [HleL HltL].
    apply (prop_to_sprop _ _
      (nd_le_correspondence _ _ _ _
        (nd_nthD_related xsR xsL n1R n1L Hxs Hn1)
        (nd_nthD_related xsR xsL n2R n2L Hxs Hn2))).
    apply HR. apply/andP; split.
    + exact (sprop_to_prop _ _
        (nd_le_correspondence _ _ _ _ Hn1 Hn2) HleL).
    + exact (sprop_to_prop _ _
        (nd_lt_correspondence _ _ _ _ Hn2
          (nd_length_related xsR xsL Hxs)) HltL).
  - intro HL. apply strictly_inhabits.
    intros n1R n2R HboundsR.
    move: HboundsR => /andP [HleR HltR].
    have Hn1 := sub_nat_rel_canonical n1R.
    have Hn2 := sub_nat_rel_canonical n2R.
    exact (sprop_to_prop _ _
      (nd_le_correspondence _ _ _ _
        (nd_nthD_related xsR xsL n1R (sub_nat_to_imported n1R) Hxs Hn1)
        (nd_nthD_related xsR xsL n2R (sub_nat_to_imported n2R) Hxs Hn2))
      (HL (sub_nat_to_imported n1R) (sub_nat_to_imported n2R)
        (Lean.And_intro _ _
          (prop_to_sprop _ _
            (nd_le_correspondence _ _ _ _ Hn1 Hn2) HleR)
          (prop_to_sprop _ _
            (nd_lt_correspondence _ _ _ _ Hn2
              (nd_length_related xsR xsL Hxs)) HltR)))).
Qed.

Theorem increasing_sequence_definition_certificate xsR xsL :
  NdNatListRel xsR xsL ->
  PropSPropRel
    (GeneratedNondecreasingSource.increasing_sequence xsR)
    (ImportedNondecreasing.Prosa_Util_Nondecreasing_increasing_sequence xsL).
Proof.
  intro Hxs. apply prop_sprop_rel_intro.
  - intros HR n1L n2L HboundsL.
    set n1R := sub_nat_to_rocq n1L.
    set n2R := sub_nat_to_rocq n2L.
    have Hn1 : SubNatRel n1R n1L := sub_nat_rel_surjective n1L.
    have Hn2 : SubNatRel n2R n2L := sub_nat_rel_surjective n2L.
    destruct HboundsL as [Hlt12L HltLenL].
    apply (prop_to_sprop _ _
      (nd_lt_correspondence _ _ _ _
        (nd_nthD_related xsR xsL n1R n1L Hxs Hn1)
        (nd_nthD_related xsR xsL n2R n2L Hxs Hn2))).
    apply HR. apply/andP; split.
    + exact (sprop_to_prop _ _
        (nd_lt_correspondence _ _ _ _ Hn1 Hn2) Hlt12L).
    + exact (sprop_to_prop _ _
        (nd_lt_correspondence _ _ _ _ Hn2
          (nd_length_related xsR xsL Hxs)) HltLenL).
  - intro HL. apply strictly_inhabits.
    intros n1R n2R HboundsR.
    move: HboundsR => /andP [Hlt12R HltLenR].
    have Hn1 := sub_nat_rel_canonical n1R.
    have Hn2 := sub_nat_rel_canonical n2R.
    exact (sprop_to_prop _ _
      (nd_lt_correspondence _ _ _ _
        (nd_nthD_related xsR xsL n1R (sub_nat_to_imported n1R) Hxs Hn1)
        (nd_nthD_related xsR xsL n2R (sub_nat_to_imported n2R) Hxs Hn2))
      (HL (sub_nat_to_imported n1R) (sub_nat_to_imported n2R)
        (Lean.And_intro _ _
          (prop_to_sprop _ _
            (nd_lt_correspondence _ _ _ _ Hn1 Hn2) Hlt12R)
          (prop_to_sprop _ _
            (nd_lt_correspondence _ _ _ _ Hn2
              (nd_length_related xsR xsL Hxs)) HltLenR)))).
Qed.

Print Assumptions nd_nat_list_source_roundtrip.
Print Assumptions nd_nat_list_target_roundtrip.
Print Assumptions nd_nat_membership_correspondence.
Print Assumptions nd_first0_related.
Print Assumptions nd_last0_related.
Print Assumptions nd_append_related.
Print Assumptions nd_max0_related.
Print Assumptions nd_le_correspondence.
Print Assumptions nd_lt_correspondence.
Print Assumptions nd_length_related.
Print Assumptions nd_nthD_related.
Print Assumptions nd_target_sub_correspondence.
Print Assumptions distances_definition_certificate.
Print Assumptions nondecreasing_sequence_definition_certificate.
Print Assumptions increasing_sequence_definition_certificate.
