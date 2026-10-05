From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq bigop.
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

(** Reusable logical composition for the three remaining interval theorems. *)
Lemma si_imp_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P -> Q) (PL -> QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros H pL. apply (prop_to_sprop _ _ HQ).
    apply H. exact (sprop_to_prop _ _ HP pL).
  - intro H. apply strictly_inhabits. intro pR.
    apply (sprop_to_prop _ _ HQ).
    apply H. exact (prop_to_sprop _ _ HP pR).
Qed.

Lemma si_and_correspondence (P Q : Prop) (PL QL : SProp) :
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

Lemma si_exists_nat_correspondence
    (PR : nat -> Prop) (PL : Lean.Nat -> SProp) :
  (forall nR nL, SubNatRel nR nL -> PropSPropRel (PR nR) (PL nL)) ->
  PropSPropRel (exists nR, PR nR) (ImportedSumInterval.Exists Lean.Nat PL).
Proof.
  intro HP. apply prop_sprop_rel_intro.
  - intros [nR Hn]. apply (ImportedSumInterval.Exists_intro Lean.Nat PL
      (sub_nat_to_imported nR)).
    exact (prop_to_sprop _ _
      (HP nR (sub_nat_to_imported nR) (sub_nat_rel_canonical nR)) Hn).
  - intros [nL Hn]. apply strictly_inhabits.
    exists (sub_nat_to_rocq nL).
    exact (sprop_to_prop _ _
      (HP (sub_nat_to_rocq nL) nL (sub_nat_rel_surjective nL)) Hn).
Qed.

(** Equal pointwise offsets over related equally sized intervals. *)
Definition si_target_big_sum_eq_statement : SProp :=
  forall (t1 t2 d : Lean.Nat) (F1 F2 : Lean.Nat -> Lean.Nat),
    (forall g : Lean.Nat,
      sum_target_lt g d ->
      Lean.eq (F1 (si_target_add t1 g)) (F2 (si_target_add t2 g))) ->
    Lean.eq
      (si_target_interval_value t1 (si_target_add t1 d) F1)
      (si_target_interval_value t2 (si_target_add t2 d) F2).

Lemma si_offset_premise_correspondence
    (t1R t2R dR : nat) (t1L t2L dL : Lean.Nat)
    (F1R F2R : nat -> nat) (F1L F2L : Lean.Nat -> Lean.Nat) :
  SubNatRel t1R t1L -> SubNatRel t2R t2L -> SubNatRel dR dL ->
  SiNatFunRel F1R F1L -> SiNatFunRel F2R F2L ->
  PropSPropRel
    (forall g, is_true (ltn g dR) ->
      Logic.eq (F1R (t1R + g)) (F2R (t2R + g)))
    (forall g, sum_target_lt g dL ->
      Lean.eq (F1L (si_target_add t1L g))
        (F2L (si_target_add t2L g))).
Proof.
  intros Ht1 Ht2 Hd HF1 HF2. apply prop_sprop_rel_intro.
  - intros HR gL HgL.
    pose gR := sub_nat_to_rocq gL.
    have Hg : SubNatRel gR gL := sub_nat_rel_surjective gL.
    apply (prop_to_sprop _ _
      (sub_nat_eq_correspondence _ _ _ _
        (HF1 _ _ (si_target_add_related _ _ _ _ Ht1 Hg))
        (HF2 _ _ (si_target_add_related _ _ _ _ Ht2 Hg)))).
    apply HR. exact (sprop_to_prop _ _
      (sub_nat_lt_correspondence _ _ _ _ Hg Hd) HgL).
  - intro HL. apply strictly_inhabits. intros gR HgR.
    have Hg := sub_nat_rel_canonical gR.
    apply (sprop_to_prop _ _
      (sub_nat_eq_correspondence _ _ _ _
        (HF1 _ _ (si_target_add_related _ _ _ _ Ht1 Hg))
        (HF2 _ _ (si_target_add_related _ _ _ _ Ht2 Hg)))).
    apply HL. exact (prop_to_sprop _ _
      (sub_nat_lt_correspondence _ _ _ _ Hg Hd) HgR).
Qed.

Lemma si_big_sum_eq_instance_correspondence
    (t1R t2R dR : nat) (t1L t2L dL : Lean.Nat)
    (F1R F2R : nat -> nat) (F1L F2L : Lean.Nat -> Lean.Nat) :
  SubNatRel t1R t1L -> SubNatRel t2R t2L -> SubNatRel dR dL ->
  SiNatFunRel F1R F1L -> SiNatFunRel F2R F2L ->
  PropSPropRel
    ((forall g, is_true (ltn g dR) ->
        Logic.eq (F1R (t1R + g)) (F2R (t2R + g))) ->
      Logic.eq
        (\sum_(t1R <= t < t1R + dR) F1R t)
        (\sum_(t2R <= t < t2R + dR) F2R t))
    ((forall g, sum_target_lt g dL ->
        Lean.eq (F1L (si_target_add t1L g))
          (F2L (si_target_add t2L g))) ->
      Lean.eq
        (si_target_interval_value t1L (si_target_add t1L dL) F1L)
        (si_target_interval_value t2L (si_target_add t2L dL) F2L)).
Proof.
  intros Ht1 Ht2 Hd HF1 HF2. apply si_imp_correspondence.
  - exact (si_offset_premise_correspondence
      t1R t2R dR t1L t2L dL F1R F2R F1L F2L
      Ht1 Ht2 Hd HF1 HF2).
  - apply sub_nat_eq_correspondence.
    + apply si_interval_sum_related; try assumption.
      exact (si_target_add_related _ _ _ _ Ht1 Hd).
    + apply si_interval_sum_related; try assumption.
      exact (si_target_add_related _ _ _ _ Ht2 Hd).
Qed.

Theorem big_sum_eq_in_eq_sized_intervals_statement_certificate :
  PropSPropRel
    GeneratedSumIntervalSource.statement_big_sum_eq_in_eq_sized_intervals
    si_target_big_sum_eq_statement.
Proof.
  unfold GeneratedSumIntervalSource.statement_big_sum_eq_in_eq_sized_intervals,
    si_target_big_sum_eq_statement.
  apply prop_sprop_rel_intro.
  - intros HR t1L t2L dL F1L F2L.
    pose t1R := sub_nat_to_rocq t1L.
    pose t2R := sub_nat_to_rocq t2L.
    pose dR := sub_nat_to_rocq dL.
    pose F1R := si_nat_fun_to_rocq F1L.
    pose F2R := si_nat_fun_to_rocq F2L.
    exact (prop_to_sprop _ _
      (si_big_sum_eq_instance_correspondence
        t1R t2R dR t1L t2L dL F1R F2R F1L F2L
        (sub_nat_rel_surjective t1L) (sub_nat_rel_surjective t2L)
        (sub_nat_rel_surjective dL) (si_nat_fun_surjective F1L)
        (si_nat_fun_surjective F2L))
      (HR t1R t2R dR F1R F2R)).
  - intro HL. apply strictly_inhabits.
    intros t1R t2R dR F1R F2R.
    exact (sprop_to_prop _ _
      (si_big_sum_eq_instance_correspondence
        t1R t2R dR (sub_nat_to_imported t1R)
        (sub_nat_to_imported t2R) (sub_nat_to_imported dR)
        F1R F2R (si_nat_fun_to_imported F1R)
        (si_nat_fun_to_imported F2R)
        (sub_nat_rel_canonical t1R) (sub_nat_rel_canonical t2R)
        (sub_nat_rel_canonical dR) (si_nat_fun_canonical F1R)
        (si_nat_fun_canonical F2R))
      (HL (sub_nat_to_imported t1R) (sub_nat_to_imported t2R)
        (sub_nat_to_imported dR) (si_nat_fun_to_imported F1R)
        (si_nat_fun_to_imported F2R))).
Qed.

(** Boolean inclusion-exclusion over an interval. *)
Definition si_source_pigeonhole_statement : Prop :=
  forall (P1 P2 : nat -> bool) (t1 t2 n1 n2 : nat),
    is_true (leq n1
      (\sum_(t1 <= t < t2) si_source_bool_nat (P1 t))) ->
    is_true (leq n2
      (\sum_(t1 <= t < t2) si_source_bool_nat (P2 t))) ->
    is_true (leq (n1 + n2 - (t2 - t1))
      (\sum_(t1 <= t < t2) si_source_bool_nat (P1 t && P2 t))).

Definition si_target_pigeonhole_statement : SProp :=
  forall (P1 P2 : Lean.Nat -> ImportedSumInterval.Bool)
      (t1 t2 n1 n2 : Lean.Nat),
    sum_target_le n1
      (si_target_interval_value t1 t2
        (fun t => si_target_bool_nat (P1 t))) ->
    sum_target_le n2
      (si_target_interval_value t1 t2
        (fun t => si_target_bool_nat (P2 t))) ->
    sum_target_le
      (si_target_sub (si_target_add n1 n2) (si_target_sub t2 t1))
      (si_target_interval_value t1 t2
        (fun t => si_target_bool_nat
          (ImportedSumInterval.Bool_and (P1 t) (P2 t)))).

Lemma si_bool_and_pred_related P1R P1L P2R P2L :
  SiBoolPredRel P1R P1L -> SiBoolPredRel P2R P2L ->
  SiBoolPredRel (fun t => P1R t && P2R t)
    (fun t => ImportedSumInterval.Bool_and (P1L t) (P2L t)).
Proof.
  intros HP1 HP2 tR tL Ht.
  exact (si_bool_and_related _ _ _ _ (HP1 _ _ Ht) (HP2 _ _ Ht)).
Qed.

Lemma si_pigeonhole_instance_correspondence
    (P1R P2R : nat -> bool)
    (P1L P2L : Lean.Nat -> ImportedSumInterval.Bool)
    (t1R t2R n1R n2R : nat) (t1L t2L n1L n2L : Lean.Nat) :
  SiBoolPredRel P1R P1L -> SiBoolPredRel P2R P2L ->
  SubNatRel t1R t1L -> SubNatRel t2R t2L ->
  SubNatRel n1R n1L -> SubNatRel n2R n2L ->
  PropSPropRel
    (is_true (leq n1R
      (\sum_(t1R <= t < t2R) si_source_bool_nat (P1R t))) ->
     is_true (leq n2R
      (\sum_(t1R <= t < t2R) si_source_bool_nat (P2R t))) ->
     is_true (leq (n1R + n2R - (t2R - t1R))
      (\sum_(t1R <= t < t2R)
        si_source_bool_nat (P1R t && P2R t))))
    (sum_target_le n1L
      (si_target_interval_value t1L t2L
        (fun t => si_target_bool_nat (P1L t))) ->
     sum_target_le n2L
      (si_target_interval_value t1L t2L
        (fun t => si_target_bool_nat (P2L t))) ->
     sum_target_le
      (si_target_sub (si_target_add n1L n2L) (si_target_sub t2L t1L))
      (si_target_interval_value t1L t2L
        (fun t => si_target_bool_nat
          (ImportedSumInterval.Bool_and (P1L t) (P2L t))))).
Proof.
  intros HP1 HP2 Ht1 Ht2 Hn1 Hn2.
  apply si_imp_correspondence.
  - apply sub_nat_le_correspondence; first exact Hn1.
    exact (si_bool_interval_sum_related _ _ _ _ _ _ Ht1 Ht2 HP1).
  - apply si_imp_correspondence.
    + apply sub_nat_le_correspondence; first exact Hn2.
      exact (si_bool_interval_sum_related _ _ _ _ _ _ Ht1 Ht2 HP2).
    + apply sub_nat_le_correspondence.
      * apply si_target_sub_related.
        -- exact (si_target_add_related _ _ _ _ Hn1 Hn2).
        -- exact (si_target_sub_related _ _ _ _ Ht2 Ht1).
      * exact (si_bool_interval_sum_related _ _ _ _ _ _ Ht1 Ht2
          (si_bool_and_pred_related _ _ _ _ HP1 HP2)).
Qed.

Theorem pigeonhole_on_interval_statement_certificate :
  PropSPropRel GeneratedSumIntervalSource.statement_pigeonhole_on_interval
    si_target_pigeonhole_statement.
Proof.
  change (PropSPropRel si_source_pigeonhole_statement
    si_target_pigeonhole_statement).
  unfold si_source_pigeonhole_statement, si_target_pigeonhole_statement.
  apply prop_sprop_rel_intro.
  - intros HR P1L P2L t1L t2L n1L n2L.
    pose P1R := si_bool_pred_to_rocq P1L.
    pose P2R := si_bool_pred_to_rocq P2L.
    exact (prop_to_sprop _ _
      (si_pigeonhole_instance_correspondence P1R P2R P1L P2L
        (sub_nat_to_rocq t1L) (sub_nat_to_rocq t2L)
        (sub_nat_to_rocq n1L) (sub_nat_to_rocq n2L)
        t1L t2L n1L n2L
        (si_bool_pred_surjective P1L) (si_bool_pred_surjective P2L)
        (sub_nat_rel_surjective t1L) (sub_nat_rel_surjective t2L)
        (sub_nat_rel_surjective n1L) (sub_nat_rel_surjective n2L))
      (HR P1R P2R (sub_nat_to_rocq t1L) (sub_nat_to_rocq t2L)
        (sub_nat_to_rocq n1L) (sub_nat_to_rocq n2L))).
  - intro HL. apply strictly_inhabits.
    intros P1R P2R t1R t2R n1R n2R.
    exact (sprop_to_prop _ _
      (si_pigeonhole_instance_correspondence P1R P2R
        (si_bool_pred_to_imported P1R) (si_bool_pred_to_imported P2R)
        t1R t2R n1R n2R (sub_nat_to_imported t1R)
        (sub_nat_to_imported t2R) (sub_nat_to_imported n1R)
        (sub_nat_to_imported n2R)
        (si_bool_pred_canonical P1R) (si_bool_pred_canonical P2R)
        (sub_nat_rel_canonical t1R) (sub_nat_rel_canonical t2R)
        (sub_nat_rel_canonical n1R) (sub_nat_rel_canonical n2R))
      (HL (si_bool_pred_to_imported P1R) (si_bool_pred_to_imported P2R)
        (sub_nat_to_imported t1R) (sub_nat_to_imported t2R)
        (sub_nat_to_imported n1R) (sub_nat_to_imported n2R))).
Qed.

(** The interval witness theorem [sum_ge_2_nat]. *)
Definition si_target_two : Lean.Nat :=
  ImportedSumInterval.OfNat_ofNat_inst1 Lean.Nat
    (Lean.Nat_succ (Lean.Nat_succ Lean.Nat_zero))
    (ImportedSumInterval.instOfNatNat
      (Lean.Nat_succ (Lean.Nat_succ Lean.Nat_zero))).

Lemma si_one_related : SubNatRel 1%N sum_target_one.
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma si_two_related : SubNatRel 2%N si_target_two.
Proof. exact (@Lean.eq_refl _ _). Qed.

Definition si_target_sum_ge_2_nat_statement : SProp :=
  forall (t1 t2 : Lean.Nat) (p : Lean.Nat -> Lean.Nat),
    (forall t, sum_target_le (p t) sum_target_one) ->
    sum_target_le si_target_two (si_target_interval_value t1 t2 p) ->
    ImportedSumInterval.Exists Lean.Nat (fun to1 =>
      ImportedSumInterval.Exists Lean.Nat (fun to2 =>
        Lean.And (sum_target_le t1 to1)
          (Lean.And (sum_target_lt to1 to2)
            (Lean.And (sum_target_lt to2 t2)
              (Lean.And
                (Lean.eq (si_target_decide_nat_eq (p to1) sum_target_one)
                  ImportedSumInterval.Bool_true)
                (Lean.eq (si_target_decide_nat_eq (p to2) sum_target_one)
                  ImportedSumInterval.Bool_true)))))).

Lemma si_pointwise_le_one_correspondence
    (pR : nat -> nat) (pL : Lean.Nat -> Lean.Nat) :
  SiNatFunRel pR pL ->
  PropSPropRel
    (forall t, is_true (leq (pR t) 1%N))
    (forall t, sum_target_le (pL t) sum_target_one).
Proof.
  intro Hp. apply prop_sprop_rel_intro.
  - intros HR tL. pose tR := sub_nat_to_rocq tL.
    exact (prop_to_sprop _ _
      (sub_nat_le_correspondence _ _ _ _
        (Hp tR tL (sub_nat_rel_surjective tL)) si_one_related)
      (HR tR)).
  - intro HL. apply strictly_inhabits. intro tR.
    exact (sprop_to_prop _ _
      (sub_nat_le_correspondence _ _ _ _
        (Hp tR (sub_nat_to_imported tR) (sub_nat_rel_canonical tR))
        si_one_related)
      (HL (sub_nat_to_imported tR))).
Qed.

Lemma si_sum_ge_2_conclusion_correspondence
    (t1R t2R : nat) (t1L t2L : Lean.Nat)
    (pR : nat -> nat) (pL : Lean.Nat -> Lean.Nat) :
  SubNatRel t1R t1L -> SubNatRel t2R t2L -> SiNatFunRel pR pL ->
  PropSPropRel
    (exists to1 to2 : nat,
      is_true (leq t1R to1) /\ is_true (ltn to1 to2) /\
      is_true (ltn to2 t2R) /\ is_true (pR to1 == 1%N) /\
      is_true (pR to2 == 1%N))
    (ImportedSumInterval.Exists Lean.Nat (fun to1 =>
      ImportedSumInterval.Exists Lean.Nat (fun to2 =>
        Lean.And (sum_target_le t1L to1)
          (Lean.And (sum_target_lt to1 to2)
            (Lean.And (sum_target_lt to2 t2L)
              (Lean.And
                (Lean.eq (si_target_decide_nat_eq (pL to1) sum_target_one)
                  ImportedSumInterval.Bool_true)
                (Lean.eq (si_target_decide_nat_eq (pL to2) sum_target_one)
                  ImportedSumInterval.Bool_true))))))).
Proof.
  intros Ht1 Ht2 Hp.
  apply si_exists_nat_correspondence. intros to1R to1L Hto1.
  apply si_exists_nat_correspondence. intros to2R to2L Hto2.
  apply si_and_correspondence.
  - exact (sub_nat_le_correspondence _ _ _ _ Ht1 Hto1).
  - apply si_and_correspondence.
    + exact (sub_nat_lt_correspondence _ _ _ _ Hto1 Hto2).
    + apply si_and_correspondence.
      * exact (sub_nat_lt_correspondence _ _ _ _ Hto2 Ht2).
      * apply si_and_correspondence.
        -- exact (si_bool_true_correspondence _ _
             (si_decide_nat_eq_related _ _ _ _
               (Hp _ _ Hto1) si_one_related)).
        -- exact (si_bool_true_correspondence _ _
             (si_decide_nat_eq_related _ _ _ _
               (Hp _ _ Hto2) si_one_related)).
Qed.

Lemma si_sum_ge_2_nat_instance_correspondence
    (t1R t2R : nat) (t1L t2L : Lean.Nat)
    (pR : nat -> nat) (pL : Lean.Nat -> Lean.Nat) :
  SubNatRel t1R t1L -> SubNatRel t2R t2L -> SiNatFunRel pR pL ->
  PropSPropRel
    ((forall t, is_true (leq (pR t) 1%N)) ->
      is_true (leq 2%N (\sum_(t1R <= t < t2R) pR t)) ->
      exists to1 to2 : nat,
        is_true (leq t1R to1) /\ is_true (ltn to1 to2) /\
        is_true (ltn to2 t2R) /\ is_true (pR to1 == 1%N) /\
        is_true (pR to2 == 1%N))
    ((forall t, sum_target_le (pL t) sum_target_one) ->
      sum_target_le si_target_two (si_target_interval_value t1L t2L pL) ->
      ImportedSumInterval.Exists Lean.Nat (fun to1 =>
        ImportedSumInterval.Exists Lean.Nat (fun to2 =>
          Lean.And (sum_target_le t1L to1)
            (Lean.And (sum_target_lt to1 to2)
              (Lean.And (sum_target_lt to2 t2L)
                (Lean.And
                  (Lean.eq (si_target_decide_nat_eq (pL to1) sum_target_one)
                    ImportedSumInterval.Bool_true)
                  (Lean.eq (si_target_decide_nat_eq (pL to2) sum_target_one)
                    ImportedSumInterval.Bool_true))))))).
Proof.
  intros Ht1 Ht2 Hp. apply si_imp_correspondence.
  - exact (si_pointwise_le_one_correspondence pR pL Hp).
  - apply si_imp_correspondence.
    + apply sub_nat_le_correspondence; first exact si_two_related.
      exact (si_interval_sum_related _ _ _ _ _ _ Ht1 Ht2 Hp).
    + exact (si_sum_ge_2_conclusion_correspondence
        t1R t2R t1L t2L pR pL Ht1 Ht2 Hp).
Qed.

Theorem sum_ge_2_nat_statement_certificate :
  PropSPropRel GeneratedSumIntervalSource.statement_sum_ge_2_nat
    si_target_sum_ge_2_nat_statement.
Proof.
  unfold GeneratedSumIntervalSource.statement_sum_ge_2_nat,
    si_target_sum_ge_2_nat_statement.
  apply prop_sprop_rel_intro.
  - intros HR t1L t2L pL.
    pose pR := si_nat_fun_to_rocq pL.
    exact (prop_to_sprop _ _
      (si_sum_ge_2_nat_instance_correspondence
        (sub_nat_to_rocq t1L) (sub_nat_to_rocq t2L) t1L t2L pR pL
        (sub_nat_rel_surjective t1L) (sub_nat_rel_surjective t2L)
        (si_nat_fun_surjective pL))
      (HR (sub_nat_to_rocq t1L) (sub_nat_to_rocq t2L) pR)).
  - intro HL. apply strictly_inhabits. intros t1R t2R pR.
    exact (sprop_to_prop _ _
      (si_sum_ge_2_nat_instance_correspondence t1R t2R
        (sub_nat_to_imported t1R) (sub_nat_to_imported t2R)
        pR (si_nat_fun_to_imported pR)
        (sub_nat_rel_canonical t1R) (sub_nat_rel_canonical t2R)
        (si_nat_fun_canonical pR))
      (HL (sub_nat_to_imported t1R) (sub_nat_to_imported t2R)
        (si_nat_fun_to_imported pR))).
Qed.

Lemma source_big_sum_eq_type_guard :
  Logic.eq GeneratedSumIntervalSource.statement_big_sum_eq_in_eq_sized_intervals
    GeneratedSumIntervalSource.statement_big_sum_eq_in_eq_sized_intervals.
Proof. reflexivity. Qed.

Lemma source_pigeonhole_type_guard :
  Logic.eq GeneratedSumIntervalSource.statement_pigeonhole_on_interval
    si_source_pigeonhole_statement.
Proof. reflexivity. Qed.

Lemma source_sum_ge_2_nat_type_guard :
  Logic.eq GeneratedSumIntervalSource.statement_sum_ge_2_nat
    GeneratedSumIntervalSource.statement_sum_ge_2_nat.
Proof. reflexivity. Qed.
