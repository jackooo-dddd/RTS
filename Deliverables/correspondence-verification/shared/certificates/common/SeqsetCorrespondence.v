From mathcomp Require Import ssreflect ssrbool eqtype seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSeqset.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation.
From prosa Require Import util.seqset.

Inductive SeqsetTrue : SProp := seqset_I.
Inductive SeqsetFalse : SProp := .

Definition seqset_false_elim (P : SProp) (H : SeqsetFalse) : P :=
  match H return P with end.
Definition SeqsetBoolTruth (b : bool) : SProp :=
  match b with true => SeqsetTrue | false => SeqsetFalse end.

Definition seqset_coq_false_to_imported
    (H : Logic.False) : ImportedSeqset.False := match H return ImportedSeqset.False with end.
Definition seqset_imported_false_to_strict
    (H : ImportedSeqset.False) : StrictlyInhabited Logic.False :=
  match H return StrictlyInhabited Logic.False with end.

Definition seqset_decidable_eq (T : eqType) : ImportedSeqset.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => ImportedSeqset.Decidable_isTrue (Lean.eq x y)
        (coq_eq_to_imported_eq x y H)
    | ReflectF H => ImportedSeqset.Decidable_isFalse (Lean.eq x y)
        (fun HL => seqset_coq_false_to_imported
          (H (imported_eq_to_coq_eq x y HL)))
    end.

Fixpoint seqset_seq_to_list {T : Type} (xs : seq T) : ImportedSeqset.List T :=
  match xs with
  | [::] => ImportedSeqset.List_nil T
  | x :: xs' => ImportedSeqset.List_cons T x (seqset_seq_to_list xs')
  end.

Fixpoint seqset_list_to_seq {T : Type} (xs : ImportedSeqset.List T) : seq T :=
  match xs with
  | ImportedSeqset.List_nil => [::]
  | ImportedSeqset.List_cons x xs' => x :: seqset_list_to_seq xs'
  end.

Lemma seqset_seq_roundtrip {T : Type} (xs : seq T) :
  Logic.eq (seqset_list_to_seq (seqset_seq_to_list xs)) xs.
Proof. induction xs; cbn; first reflexivity. f_equal. exact IHxs. Qed.

Definition seqset_strict_uniq_transport {T : eqType} (xs ys : seq T) :
    Logic.eq xs ys -> StrictlyInhabited (uniq xs) ->
    StrictlyInhabited (uniq ys) :=
  fun H Huniq =>
    match H in Logic.eq _ zs return StrictlyInhabited (uniq zs) with
    | Logic.eq_refl => Huniq
    end.

Definition seqset_list_cons_congr {T : Type} (x : T)
    (xs ys : ImportedSeqset.List T) :
    Lean.eq xs ys ->
    Lean.eq (ImportedSeqset.List_cons T x xs)
      (ImportedSeqset.List_cons T x ys) :=
  fun H => match H in Lean.eq _ zs return
      Lean.eq (ImportedSeqset.List_cons T x xs)
        (ImportedSeqset.List_cons T x zs) with
    | Lean.eq_refl => @Lean.eq_refl (ImportedSeqset.List T)
        (ImportedSeqset.List_cons T x xs)
    end.

Lemma seqset_list_roundtrip {T : Type} (xs : ImportedSeqset.List T) :
  Lean.eq (seqset_seq_to_list (seqset_list_to_seq xs)) xs.
Proof.
  induction xs as [|x xs IH]; cbn.
  - exact (@Lean.eq_refl (ImportedSeqset.List T) (ImportedSeqset.List_nil T)).
  - exact (seqset_list_cons_congr x _ _ IH).
Qed.

Definition seqset_list_mem_transport {T : Type} (x : T)
    (xs ys : ImportedSeqset.List T) :
    Lean.eq xs ys -> ImportedSeqset.List_Mem T x xs ->
    ImportedSeqset.List_Mem T x ys :=
  fun Hxy Hmem =>
    match Hxy in Lean.eq _ zs return ImportedSeqset.List_Mem T x zs with
    | Lean.eq_refl => Hmem
    end.

Definition seqset_bool_prop_to_truth (b : bool) :
    is_true b -> SeqsetBoolTruth b :=
  match b return is_true b -> SeqsetBoolTruth b with
  | true => fun _ => seqset_I
  | false => fun H =>
      match H in Logic.eq _ z return
        match z with true => SeqsetFalse | false => SeqsetTrue end
      with Logic.eq_refl => seqset_I end
  end.

Definition seqset_or_left (a b : bool) :
    SeqsetBoolTruth a -> SeqsetBoolTruth (a || b) :=
  match a, b return SeqsetBoolTruth a -> SeqsetBoolTruth (a || b) with
  | true, _ => fun _ => seqset_I
  | false, true => fun _ => seqset_I
  | false, false => fun H => H
  end.
Definition seqset_or_right (a b : bool) :
    SeqsetBoolTruth b -> SeqsetBoolTruth (a || b) :=
  match a, b return SeqsetBoolTruth b -> SeqsetBoolTruth (a || b) with
  | _, true => fun _ => seqset_I
  | true, false => fun _ => seqset_I
  | false, false => fun H => H
  end.

Definition seqset_eq_refl_truth (T : eqType) (x : T) :
    SeqsetBoolTruth (x == x).
Proof. rewrite eqxx. exact seqset_I. Defined.

Definition seqset_mem_head {T : Type} (x y : T)
    (xs : ImportedSeqset.List T) : Logic.eq x y ->
    ImportedSeqset.List_Mem T x (ImportedSeqset.List_cons T y xs) :=
  fun H => match H in Logic.eq _ z return
      ImportedSeqset.List_Mem T x (ImportedSeqset.List_cons T z xs) with
    | Logic.eq_refl => ImportedSeqset.List_Mem_head T x xs
    end.

Fixpoint seqset_mem_forward {T : eqType} (x : T) (xs : seq T) :
    SeqsetBoolTruth (x \in xs) ->
    ImportedSeqset.List_Mem T x (seqset_seq_to_list xs) :=
  match xs as xs0 return SeqsetBoolTruth (x \in xs0) ->
      ImportedSeqset.List_Mem T x (seqset_seq_to_list xs0) with
  | [::] => seqset_false_elim _
  | y :: ys =>
      match @eqP T x y as r in reflect _ b return
        SeqsetBoolTruth (b || (x \in ys)) ->
        ImportedSeqset.List_Mem T x
          (ImportedSeqset.List_cons T y (seqset_seq_to_list ys))
      with
      | ReflectT Hxy => fun _ => seqset_mem_head x y _ Hxy
      | ReflectF _ => fun H => ImportedSeqset.List_Mem_tail T x y _
          (seqset_mem_forward x ys H)
      end
  end.

Lemma seqset_mem_tail_source {T : eqType} (x y : T) (xs : seq T) :
  x \in xs -> x \in y :: xs.
Proof. rewrite in_cons. move=> H. apply/orP. right. exact H. Qed.

Fixpoint seqset_imported_mem_to_strict {T : eqType} (x : T)
    (xs : ImportedSeqset.List T) (H : ImportedSeqset.List_Mem T x xs) :
    StrictlyInhabited (x \in seqset_list_to_seq xs) :=
  match H with
  | ImportedSeqset.List_Mem_head ys =>
      strictly_inhabits (mem_head x (seqset_list_to_seq ys))
  | ImportedSeqset.List_Mem_tail y ys Htail =>
      match seqset_imported_mem_to_strict x ys Htail with
      | strictly_inhabits Hmem =>
          strictly_inhabits
            (seqset_mem_tail_source x y (seqset_list_to_seq ys) Hmem)
      end
  end.

Definition seqset_and_left (a b : bool) :
    SeqsetBoolTruth (a && b) -> SeqsetBoolTruth a :=
  match a, b return SeqsetBoolTruth (a && b) -> SeqsetBoolTruth a with
  | true, _ => fun _ => seqset_I
  | false, _ => fun H => H
  end.

Definition seqset_and_right (a b : bool) :
    SeqsetBoolTruth (a && b) -> SeqsetBoolTruth b :=
  match a, b return SeqsetBoolTruth (a && b) -> SeqsetBoolTruth b with
  | true, true => fun _ => seqset_I
  | true, false => fun H => H
  | false, true => fun _ => seqset_I
  | false, false => fun H => H
  end.

Definition seqset_neg_mem_contra (b : bool) :
    SeqsetBoolTruth (~~ b) -> SeqsetBoolTruth b -> ImportedSeqset.False :=
  match b return
      SeqsetBoolTruth (~~ b) -> SeqsetBoolTruth b -> ImportedSeqset.False with
  | true => fun H _ => seqset_false_elim _ H
  | false => fun _ H => seqset_false_elim _ H
  end.

Fixpoint source_uniq_truth_to_imported_nodup {T : eqType} (xs : seq T) :
    SeqsetBoolTruth (uniq xs) ->
    ImportedSeqset.List_Nodup T (seqset_seq_to_list xs).
Proof.
  destruct xs as [|x xs].
  - intro Hnil. exact (ImportedSeqset.List_Pairwise_nil T (ImportedSeqset.Ne T)).
  - intro Huniq.
    apply ImportedSeqset.List_Pairwise_cons.
    + intros y Hy Hxy.
      have HyR0 := interpret_strict _
        (seqset_imported_mem_to_strict y (seqset_seq_to_list xs) Hy).
      have HyR : y \in xs.
      { rewrite -(seqset_seq_roundtrip xs). exact HyR0. }
      have Hcoq : Logic.eq x y := imported_eq_to_coq_eq x y Hxy.
      subst y.
      exact (seqset_neg_mem_contra (x \in xs)
        (seqset_and_left _ _ Huniq)
        (seqset_bool_prop_to_truth _ HyR)).
    + exact (@source_uniq_truth_to_imported_nodup T xs
        (seqset_and_right _ _ Huniq)).
Defined.

Definition source_uniq_to_imported_nodup {T : eqType} (xs : seq T)
    (H : uniq xs) : ImportedSeqset.List_Nodup T (seqset_seq_to_list xs) :=
  source_uniq_truth_to_imported_nodup xs
    (seqset_bool_prop_to_truth _ H).

Lemma imported_nodup_to_strict_source_uniq {T : eqType}
    (xs : ImportedSeqset.List T) :
    ImportedSeqset.List_Nodup T xs ->
    StrictlyInhabited (uniq (seqset_list_to_seq xs)).
Proof.
  intro Hnodup. induction Hnodup as [|x xs Hpair Htail IH].
  - exact (strictly_inhabits (Logic.eq_refl true)).
  - destruct IH as [IHuniq]. apply strictly_inhabits.
    apply/andP. split; last exact IHuniq.
    apply/negP. intro Hmem.
    have HmemL := seqset_mem_forward x (seqset_list_to_seq xs)
      (seqset_bool_prop_to_truth _ Hmem).
    have Hneq := Hpair x (seqset_list_mem_transport x _ _
      (seqset_list_roundtrip xs) HmemL).
    have Hfalse := Hneq (@Lean.eq_refl T x).
    exact (interpret_strict Logic.False
      (seqset_imported_false_to_strict Hfalse)).
Qed.

Definition RocqSeqSetRel (T : eqType)
    (sR : @prosa.util.seqset.set T)
    (sL : Prosa_Util_Seqset_set T (seqset_decidable_eq T)) : SProp :=
  Lean.eq (seqset_seq_to_list (@prosa.util.seqset._set_seq T sR))
    (Prosa_Util_Seqset_set_val T (seqset_decidable_eq T) sL).

Definition source_to_imported_seqset (T : eqType)
    (s : @prosa.util.seqset.set T) :
    Prosa_Util_Seqset_set T (seqset_decidable_eq T).
Proof.
  destruct s as [xs Huniq].
  exact (Prosa_Util_Seqset_set_mk T (seqset_decidable_eq T)
    (seqset_seq_to_list xs) (source_uniq_to_imported_nodup xs Huniq)).
Defined.

Definition imported_to_source_seqset (T : eqType)
    (s : Prosa_Util_Seqset_set T (seqset_decidable_eq T)) :
    @prosa.util.seqset.set T.
Proof.
  destruct s as [xs Hnodup].
  refine (@prosa.util.seqset.Build_set T (seqset_list_to_seq xs) _).
  exact (interpret_strict _ (imported_nodup_to_strict_source_uniq xs Hnodup)).
Defined.

Lemma seqset_relation_source_total (T : eqType)
    (s : @prosa.util.seqset.set T) :
  RocqSeqSetRel T s (source_to_imported_seqset T s).
Proof. destruct s. exact (@Lean.eq_refl _ _). Qed.

Lemma seqset_source_roundtrip_observable (T : eqType)
    (s : @prosa.util.seqset.set T) :
  Logic.eq
    (@prosa.util.seqset._set_seq T
      (imported_to_source_seqset T (source_to_imported_seqset T s)))
    (@prosa.util.seqset._set_seq T s).
Proof. destruct s as [xs Huniq]. exact (seqset_seq_roundtrip xs). Qed.

Lemma seqset_imported_roundtrip_observable (T : eqType)
    (s : Prosa_Util_Seqset_set T (seqset_decidable_eq T)) :
  Lean.eq
    (Prosa_Util_Seqset_set_val T (seqset_decidable_eq T)
      (source_to_imported_seqset T (imported_to_source_seqset T s)))
    (Prosa_Util_Seqset_set_val T (seqset_decidable_eq T) s).
Proof. destruct s as [xs Hnodup]. exact (seqset_list_roundtrip xs). Qed.

Print Assumptions source_uniq_to_imported_nodup.
Print Assumptions imported_nodup_to_strict_source_uniq.
Print Assumptions seqset_relation_source_total.
Print Assumptions seqset_source_roundtrip_observable.
Print Assumptions seqset_imported_roundtrip_observable.
