From mathcomp Require Import ssreflect ssrbool ssrnat seq bigop.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSumInterval ImportedSubadditivity.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  SumIntervalCorrespondence.
Require Import GeneratedSumIntervalSource.

Definition sum_target_le (a b : Lean.Nat) : SProp :=
  ImportedSumInterval.LE_le_inst1 Lean.Nat
    ImportedSumInterval.instLENat a b.

Definition sum_target_lt (a b : Lean.Nat) : SProp :=
  ImportedSumInterval.LT_lt_inst1 Lean.Nat
    ImportedSumInterval.instLTNat a b.

Lemma sum_target_le_forward (a b : nat) :
  is_true (leq a b) ->
  sum_target_le (sub_nat_to_imported a) (sub_nat_to_imported b).
Proof.
  intro H.
  exact (prop_to_sprop _ _
    (sub_nat_le_correspondence a (sub_nat_to_imported a)
      b (sub_nat_to_imported b) (sub_nat_rel_canonical a)
      (sub_nat_rel_canonical b)) H).
Qed.

Lemma sum_target_le_backward (a b : nat) :
  sum_target_le (sub_nat_to_imported a) (sub_nat_to_imported b) ->
  is_true (leq a b).
Proof.
  intro H.
  exact (sprop_to_prop _ _
    (sub_nat_le_correspondence a (sub_nat_to_imported a)
      b (sub_nat_to_imported b) (sub_nat_rel_canonical a)
      (sub_nat_rel_canonical b)) H).
Qed.

Lemma sum_target_lt_forward (a b : nat) :
  is_true (ltn a b) ->
  sum_target_lt (sub_nat_to_imported a) (sub_nat_to_imported b).
Proof.
  intro H.
  exact (prop_to_sprop _ _
    (sub_nat_lt_correspondence a (sub_nat_to_imported a)
      b (sub_nat_to_imported b) (sub_nat_rel_canonical a)
      (sub_nat_rel_canonical b)) H).
Qed.

Lemma sum_target_lt_backward (a b : nat) :
  sum_target_lt (sub_nat_to_imported a) (sub_nat_to_imported b) ->
  is_true (ltn a b).
Proof.
  intro H.
  exact (sprop_to_prop _ _
    (sub_nat_lt_correspondence a (sub_nat_to_imported a)
      b (sub_nat_to_imported b) (sub_nat_rel_canonical a)
      (sub_nat_rel_canonical b)) H).
Qed.

Lemma sum_target_decode_zero (n : nat) :
  Lean.eq (sub_nat_to_imported n) Lean.Nat_zero -> Logic.eq n O.
Proof.
  intro H.
  have Hdecoded := f_equal sub_nat_to_rocq
    (imported_eq_to_coq_eq _ _ H).
  rw sub_nat_rocq_roundtrip in Hdecoded.
  exact Hdecoded.
Qed.

Definition source_big_nat_eq0_statement
    (m n : nat) (F : nat -> nat) : Prop :=
  Logic.eq (\sum_(m <= i < n) F i) O <->
  forall i, leq m i && ltn i n -> Logic.eq (F i) O.

Definition target_big_nat_eq0_statement
    (m n : nat) (F : nat -> nat) : SProp :=
  ImportedSumInterval.Iff
    (Lean.eq (sum_target_interval_value m n F) Lean.Nat_zero)
    (forall i : Lean.Nat,
      Lean.And
        (sum_target_le (sub_nat_to_imported m) i)
        (sum_target_lt i (sub_nat_to_imported n)) ->
      Lean.eq (sum_target_function F i) Lean.Nat_zero).

Lemma sum_big_pointwise_forward (m n : nat) (F : nat -> nat)
    (Hall : forall i, leq m i && ltn i n -> Logic.eq (F i) O) :
  forall i : Lean.Nat,
    Lean.And
      (sum_target_le (sub_nat_to_imported m) i)
      (sum_target_lt i (sub_nat_to_imported n)) ->
    Lean.eq (sum_target_function F i) Lean.Nat_zero.
Proof.
  intros i Hbounds. destruct Hbounds as [Hlow Hhigh].
  have Hround := sub_nat_imported_roundtrip i.
  have HlowC := sub_imported_le_transport _ _ _ _
    (@Lean.eq_refl Lean.Nat (sub_nat_to_imported m))
    (sub_imported_eq_sym _ _ Hround) Hlow.
  have HhighC := sub_imported_le_transport _ _ _ _
    (sub_imported_eq_congr Lean.Nat_succ _ _
      (sub_imported_eq_sym _ _ Hround))
    (@Lean.eq_refl Lean.Nat (sub_nat_to_imported n)) Hhigh.
  have Hzero := Hall (sub_nat_to_rocq i).
  have HzeroR : Logic.eq (F (sub_nat_to_rocq i)) O.
  { apply Hzero. apply/andP. split.
    - exact (sum_target_le_backward m (sub_nat_to_rocq i) HlowC).
    - exact (sum_target_lt_backward (sub_nat_to_rocq i) n HhighC). }
  unfold sum_target_function. rw HzeroR.
  exact (@Lean.eq_refl Lean.Nat Lean.Nat_zero).
Qed.

Lemma sum_target_zero_to_source_point_strict
    (m n : nat) (F : nat -> nat)
    (Hzero : Lean.eq (sum_target_interval_value m n F) Lean.Nat_zero ->
      forall i : Lean.Nat,
        Lean.And
          (sum_target_le (sub_nat_to_imported m) i)
          (sum_target_lt i (sub_nat_to_imported n)) ->
        Lean.eq (sum_target_function F i) Lean.Nat_zero)
    (HsourceZero : Logic.eq (\sum_(m <= i < n) F i) O) :
  StrictlyInhabited
    (forall i, leq m i && ltn i n -> Logic.eq (F i) O).
Proof.
  apply strictly_inhabits. intros i Hi. move/andP: Hi => [Hlow Hhigh].
  have HtargetZero : Lean.eq (sum_target_interval_value m n F)
      Lean.Nat_zero :=
    sub_imported_eq_trans _ _ _
      (finite_nat_sum_value_correspondence m n F)
      (coq_eq_to_imported_eq _ _
        (f_equal sub_nat_to_imported HsourceZero)).
  have Heq := Hzero HtargetZero (sub_nat_to_imported i)
    (Lean.And_intro _ _
      (sum_target_le_forward m i Hlow)
      (sum_target_lt_forward i n Hhigh)).
  unfold sum_target_function in Heq. rw sub_nat_rocq_roundtrip in Heq.
  exact (sum_target_decode_zero _ Heq).
Qed.

Lemma sum_target_point_to_source_zero_strict
    (m n : nat) (F : nat -> nat)
    (Hpoint : (forall i : Lean.Nat,
      Lean.And
        (sum_target_le (sub_nat_to_imported m) i)
        (sum_target_lt i (sub_nat_to_imported n)) ->
      Lean.eq (sum_target_function F i) Lean.Nat_zero) ->
      Lean.eq (sum_target_interval_value m n F) Lean.Nat_zero)
    (Hall : forall i, leq m i && ltn i n -> Logic.eq (F i) O) :
  StrictlyInhabited (Logic.eq (\sum_(m <= i < n) F i) O).
Proof.
  have HtargetZero := Hpoint (sum_big_pointwise_forward m n F Hall).
  have Hcanonical := sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _
      (finite_nat_sum_value_correspondence m n F)) HtargetZero.
  apply strictly_inhabits. exact (sum_target_decode_zero _ Hcanonical).
Qed.

Theorem big_nat_eq0_statement_certificate (m n : nat) (F : nat -> nat) :
  PropSPropRel
    (source_big_nat_eq0_statement m n F)
    (target_big_nat_eq0_statement m n F).
Proof.
  apply prop_sprop_rel_intro.
  - intro Hsource. destruct Hsource as [Hzero Hpoint].
    apply (ImportedSumInterval.Iff_intro _ _).
    + intro HsumZero.
      have Hcanonical := sub_imported_eq_trans _ _ _
        (sub_imported_eq_sym _ _
          (finite_nat_sum_value_correspondence m n F)) HsumZero.
      have HsourceZero := sum_target_decode_zero _ Hcanonical.
      intros i Hbounds. destruct Hbounds as [Hlow Hhigh].
      have Hround := sub_nat_imported_roundtrip i.
      have HlowC := sub_imported_le_transport _ _ _ _
        (@Lean.eq_refl Lean.Nat (sub_nat_to_imported m))
        (sub_imported_eq_sym _ _ Hround) Hlow.
      have HhighC := sub_imported_le_transport _ _ _ _
        (sub_imported_eq_congr Lean.Nat_succ _ _
          (sub_imported_eq_sym _ _ Hround))
        (@Lean.eq_refl Lean.Nat (sub_nat_to_imported n)) Hhigh.
      have HiZero := Hzero HsourceZero (sub_nat_to_rocq i).
      have HiZero' : Logic.eq (F (sub_nat_to_rocq i)) O.
      { apply HiZero. apply/andP. split.
        - exact (sum_target_le_backward m (sub_nat_to_rocq i) HlowC).
        - exact (sum_target_lt_backward (sub_nat_to_rocq i) n HhighC). }
      unfold sum_target_function. rw HiZero'.
      exact (@Lean.eq_refl Lean.Nat Lean.Nat_zero).
    + intro Hall.
      have HsourceZero : Logic.eq (\sum_(m <= i < n) F i) O.
      { apply Hpoint. intros i Hi. move/andP: Hi => [Hlow Hhigh].
        have Heq := Hall (sub_nat_to_imported i)
          (Lean.And_intro _ _
            (sum_target_le_forward m i Hlow)
            (sum_target_lt_forward i n Hhigh)).
        unfold sum_target_function in Heq.
        rw sub_nat_rocq_roundtrip in Heq.
        exact (sum_target_decode_zero _ Heq). }
      have Hsum := finite_nat_sum_value_correspondence m n F.
      rw HsourceZero in Hsum. exact Hsum.
  - intro Htarget. destruct Htarget as [Hzero Hpoint].
    apply strictly_inhabits. split.
    + intro HsumZero.
      exact (interpret_strict _
        (sum_target_zero_to_source_point_strict
          m n F Hzero HsumZero)).
    + intro Hall.
      exact (interpret_strict _
        (sum_target_point_to_source_zero_strict
          m n F Hpoint Hall)).
Qed.

Definition source_sum_of_ones_statement (t delta : nat) : Prop :=
  Logic.eq (\sum_(t <= x < t + delta) 1) delta.

Definition target_sum_of_ones_value (t delta : nat) : Lean.Nat :=
  ImportedSumInterval.List_foldr_inst3 Lean.Nat Lean.Nat
    Lean.Nat_add Lean.Nat_zero
    (ImportedSumInterval.List_map_inst3 Lean.Nat Lean.Nat
      (fun _ : Lean.Nat => sum_target_one)
      (ImportedSumInterval.List_range'
        (sub_nat_to_imported t)
        (ImportedSumInterval.Nat_sub
          (Lean.Nat_add (sub_nat_to_imported t)
            (sub_nat_to_imported delta))
          (sub_nat_to_imported t))
        sum_target_one)).

Definition target_sum_of_ones_statement (t delta : nat) : SProp :=
  Lean.eq (target_sum_of_ones_value t delta)
    (sub_nat_to_imported delta).

Lemma target_sum_of_ones_value_prop (t delta : nat) :
  Logic.eq (target_sum_of_ones_value t delta)
    (sub_nat_to_imported (\sum_(t <= x < t + delta) 1)).
Proof.
  unfold target_sum_of_ones_value.
  rw sum_target_add_canonical_prop.
  change (Logic.eq
    (sum_target_interval_value t (t + delta) (fun _ : nat => 1%N))
    (sub_nat_to_imported (\sum_(t <= x < t + delta) 1))).
  exact (sum_target_interval_value_prop t (t + delta)
    (fun _ : nat => 1%N)).
Qed.

Lemma sub_nat_to_imported_injective (a b : nat) :
  Logic.eq (sub_nat_to_imported a) (sub_nat_to_imported b) ->
  Logic.eq a b.
Proof.
  intro H. have Hdecoded := f_equal sub_nat_to_rocq H.
  now rw !sub_nat_rocq_roundtrip in Hdecoded.
Qed.

Theorem sum_of_ones_statement_certificate (t delta : nat) :
  PropSPropRel
    (source_sum_of_ones_statement t delta)
    (target_sum_of_ones_statement t delta).
Proof.
  apply prop_sprop_rel_intro.
  - intro Hsource. apply coq_eq_to_imported_eq.
    rw target_sum_of_ones_value_prop Hsource. reflexivity.
  - intro Htarget. apply strictly_inhabits.
    apply sub_nat_to_imported_injective.
    rw -target_sum_of_ones_value_prop.
    exact (imported_eq_to_coq_eq _ _ Htarget).
Qed.

Definition source_sum_le_range_statement
    (f : nat -> nat) (t delta : nat) : Prop :=
  ltn (\sum_(t <= x < t + delta) f x) delta ->
  exists x, (leq t x && ltn x (t + delta)) /\ Logic.eq (f x) O.

Definition target_sum_le_range_value
    (f : nat -> nat) (t delta : nat) : Lean.Nat :=
  ImportedSumInterval.List_foldr_inst3 Lean.Nat Lean.Nat
    Lean.Nat_add Lean.Nat_zero
    (ImportedSumInterval.List_map_inst3 Lean.Nat Lean.Nat
      (sum_target_function f)
      (ImportedSumInterval.List_range'
        (sub_nat_to_imported t)
        (ImportedSumInterval.Nat_sub
          (Lean.Nat_add (sub_nat_to_imported t)
            (sub_nat_to_imported delta))
          (sub_nat_to_imported t))
        sum_target_one)).

Definition target_sum_le_range_statement
    (f : nat -> nat) (t delta : nat) : SProp :=
  sum_target_lt (target_sum_le_range_value f t delta)
      (sub_nat_to_imported delta) ->
  ImportedSumInterval.Exists Lean.Nat (fun x =>
    Lean.And
      (sum_target_le (sub_nat_to_imported t) x)
      (Lean.And
        (sum_target_lt x
          (Lean.Nat_add (sub_nat_to_imported t)
            (sub_nat_to_imported delta)))
        (Lean.eq (sum_target_function f x) Lean.Nat_zero))).

Lemma target_sum_le_range_value_prop
    (f : nat -> nat) (t delta : nat) :
  Logic.eq (target_sum_le_range_value f t delta)
    (sub_nat_to_imported (\sum_(t <= x < t + delta) f x)).
Proof.
  unfold target_sum_le_range_value.
  rw sum_target_add_canonical_prop.
  change (Logic.eq (sum_target_interval_value t (t + delta) f)
    (sub_nat_to_imported (\sum_(t <= x < t + delta) f x))).
  exact (sum_target_interval_value_prop t (t + delta) f).
Qed.

Definition sum_and_left (a b : bool) :
    is_true (a && b) -> is_true a :=
  match a, b return is_true (a && b) -> is_true a with
  | true, true => fun _ => Logic.eq_refl true
  | true, false => fun _ => Logic.eq_refl true
  | false, true => fun H => H
  | false, false => fun H => H
  end.

Definition sum_and_right (a b : bool) :
    is_true (a && b) -> is_true b :=
  match a, b return is_true (a && b) -> is_true b with
  | true, true => fun _ => Logic.eq_refl true
  | true, false => fun H => H
  | false, true => fun _ => Logic.eq_refl true
  | false, false => fun H => H
  end.

Lemma sum_le_range_exists_backward_strict
    (f : nat -> nat) (t delta : nat)
    (H : ImportedSumInterval.Exists Lean.Nat (fun x =>
      Lean.And
        (sum_target_le (sub_nat_to_imported t) x)
        (Lean.And
          (sum_target_lt x
            (Lean.Nat_add (sub_nat_to_imported t)
              (sub_nat_to_imported delta)))
          (Lean.eq (sum_target_function f x) Lean.Nat_zero)))) :
  StrictlyInhabited
    (exists x, (leq t x && ltn x (t + delta)) /\ Logic.eq (f x) O).
Proof.
  destruct H as [xL Hparts].
  destruct Hparts as [Hlow Hrest]. destruct Hrest as [Hhigh Hzero].
  apply strictly_inhabits.
  exists (sub_nat_to_rocq xL). split.
  - apply/andP. split.
    + have Hround := sub_nat_imported_roundtrip xL.
      have HlowC := sub_imported_le_transport _ _ _ _
        (@Lean.eq_refl Lean.Nat (sub_nat_to_imported t))
        (sub_imported_eq_sym _ _ Hround) Hlow.
      exact (sum_target_le_backward t (sub_nat_to_rocq xL) HlowC).
    + have Hround := sub_nat_imported_roundtrip xL.
      have HhighX := sub_imported_le_transport _ _ _ _
        (sub_imported_eq_congr Lean.Nat_succ _ _
          (sub_imported_eq_sym _ _ Hround))
        (@Lean.eq_refl Lean.Nat
          (Lean.Nat_add (sub_nat_to_imported t)
            (sub_nat_to_imported delta))) Hhigh.
      have HhighC := sub_imported_le_transport _ _ _ _
        (@Lean.eq_refl Lean.Nat
          (Lean.Nat_succ (sub_nat_to_imported (sub_nat_to_rocq xL))))
        (sum_target_add_canonical t delta) HhighX.
      exact (sum_target_lt_backward (sub_nat_to_rocq xL)
        (t + delta) HhighC).
  - unfold sum_target_function in Hzero.
    exact (sum_target_decode_zero _ Hzero).
Qed.

Theorem sum_le_summation_range_statement_certificate
    (f : nat -> nat) (t delta : nat) :
  PropSPropRel
    (source_sum_le_range_statement f t delta)
    (target_sum_le_range_statement f t delta).
Proof.
  apply prop_sprop_rel_intro.
  - intro Hsource. intro HltL.
    have Hvalue := coq_eq_to_imported_eq _ _
      (target_sum_le_range_value_prop f t delta).
    have HltC := sub_imported_le_transport _ _ _ _
      (sub_imported_eq_congr Lean.Nat_succ _ _ Hvalue)
      (@Lean.eq_refl Lean.Nat (sub_nat_to_imported delta)) HltL.
    have HltR := sum_target_lt_backward
      (\sum_(t <= x < t + delta) f x) delta HltC.
    destruct (Hsource HltR) as [x Hx].
    apply (ImportedSumInterval.Exists_intro Lean.Nat _
      (sub_nat_to_imported x)).
    apply (Lean.And_intro _ _
      (sum_target_le_forward _ _ (sum_and_left _ _ (Logic.proj1 Hx)))).
    apply (Lean.And_intro _ _).
    + have Hupper := sum_target_lt_forward _ _
        (sum_and_right _ _ (Logic.proj1 Hx)).
      exact (sub_imported_le_transport _ _ _ _
        (@Lean.eq_refl Lean.Nat (Lean.Nat_succ (sub_nat_to_imported x)))
        (sub_imported_eq_sym _ _ (sum_target_add_canonical t delta)) Hupper).
    + unfold sum_target_function. rw sub_nat_rocq_roundtrip (Logic.proj2 Hx).
      exact (@Lean.eq_refl Lean.Nat Lean.Nat_zero).
  - intro Htarget. apply strictly_inhabits. intro HltR.
    have Hvalue := coq_eq_to_imported_eq _ _
      (target_sum_le_range_value_prop f t delta).
    have HltC := sum_target_lt_forward
      (\sum_(t <= x < t + delta) f x) delta HltR.
    have HltL := sub_imported_le_transport _ _ _ _
      (sub_imported_eq_congr Lean.Nat_succ _ _
        (sub_imported_eq_sym _ _ Hvalue))
      (@Lean.eq_refl Lean.Nat (sub_nat_to_imported delta)) HltC.
    exact (interpret_strict _
      (sum_le_range_exists_backward_strict f t delta (Htarget HltL))).
Qed.

(** Definitional guards that bind the independently proved semantic shells to
    the exact automatically extracted source statement definitions. *)
Lemma source_sum_of_ones_type_guard :
  Logic.eq GeneratedSumIntervalSource.statement_sum_of_ones
    (forall t delta, source_sum_of_ones_statement t delta).
Proof. reflexivity. Qed.

Lemma source_big_nat_eq0_type_guard :
  Logic.eq GeneratedSumIntervalSource.statement_big_nat_eq0
    (forall m n F, source_big_nat_eq0_statement m n F).
Proof. reflexivity. Qed.

Lemma source_sum_le_range_type_guard :
  Logic.eq GeneratedSumIntervalSource.statement_sum_le_summation_range
    (forall f t delta, source_sum_le_range_statement f t delta).
Proof. reflexivity. Qed.
