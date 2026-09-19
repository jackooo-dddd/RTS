From mathcomp Require Import ssreflect ssrbool ssrnat seq bigop.
From LeanImport Require Import Lean.
Require Import ImportedFiniteNatSumNormalized93 ImportedBigNatEq093
  PropSPropFoundation HardSumCertificate
  FiniteNatSumBridge.
From HardSource Require Import Generated_util__sum.

Definition source_sum_of_ones_statement (t delta : nat) : Prop :=
  Logic.eq (\sum_(t <= x < t + delta) 1) delta.

Definition imported_sum_of_ones_value (t delta : nat) : Nat :=
  ImportedFiniteNatSumNormalized93.List_foldr_inst3 Nat Nat
    (fun x y : Nat => Nat_add x y) Nat_zero
    (ImportedFiniteNatSumNormalized93.List_map_inst3 Nat Nat
      (fun _ : Nat =>
        ImportedFiniteNatSumNormalized93.OfNat_ofNat_inst1 Nat 1
          (ImportedFiniteNatSumNormalized93.instOfNatNat 1))
      (ImportedFiniteNatSumNormalized93.List_range' (sum_nat_to_imported t)
        (ImportedFiniteNatSumNormalized93.Nat_sub
          (Nat_add
            (sum_nat_to_imported t) (sum_nat_to_imported delta))
          (sum_nat_to_imported t))
        (ImportedFiniteNatSumNormalized93.OfNat_ofNat_inst1 Nat 1
          (ImportedFiniteNatSumNormalized93.instOfNatNat 1)))).

Definition imported_sum_of_ones_statement (t delta : nat) : SProp :=
  eq (imported_sum_of_ones_value t delta) (sum_nat_to_imported delta).

Definition original_sum_of_ones_has_expected_statement (t delta : nat) :
    source_sum_of_ones_statement t delta :=
  @Generated_util__sum.sum_of_ones t delta.

Lemma imported_sum_of_ones_has_expected_statement (t delta : nat) :
  imported_sum_of_ones_statement t delta.
Proof.
  unfold imported_sum_of_ones_statement, imported_sum_of_ones_value,
    imported_one.
  exact (ImportedFiniteNatSumNormalized93.Prosa_Util_Sum_sum_of_ones
    (sum_nat_to_imported t) (sum_nat_to_imported delta)).
Qed.

Lemma imported_sum_of_ones_value_prop (t delta : nat) :
  Logic.eq (imported_sum_of_ones_value t delta)
    (sum_nat_to_imported (\sum_(t <= x < t + delta) 1)).
Proof.
  unfold imported_sum_of_ones_value.
  rewrite imported_add_canonical_prop.
  change (Logic.eq
    (imported_interval_sum t (t + delta) (fun _ : nat => 1%N))
    (sum_nat_to_imported (\sum_(t <= x < t + delta) 1))).
  exact (finite_nat_sum_value_bridge_prop t (t + delta)
    (fun _ : nat => 1%N)).
Qed.

Lemma sum_nat_to_imported_injective_prop (a b : nat) :
  Logic.eq (sum_nat_to_imported a) (sum_nat_to_imported b) ->
  Logic.eq a b.
Proof.
  intro H.
  have Hdecoded := f_equal sum_imported_nat_to_rocq H.
  now rewrite !sum_rocq_roundtrip in Hdecoded.
Qed.

Theorem sum_of_ones_statement_certificate (t delta : nat) :
  PropSPropRel
    (source_sum_of_ones_statement t delta)
    (imported_sum_of_ones_statement t delta).
Proof.
  apply prop_sprop_rel_intro.
  - intro Hsource.
    apply coq_eq_to_imported_eq.
    rewrite imported_sum_of_ones_value_prop Hsource. reflexivity.
  - intro Htarget. apply strictly_inhabits.
    have HtargetP := interpret_strict _
      (imported_eq_to_strict_eq _ _ Htarget).
    apply sum_nat_to_imported_injective_prop.
    rewrite -imported_sum_of_ones_value_prop. exact HtargetP.
Qed.

Print Assumptions original_sum_of_ones_has_expected_statement.
Print Assumptions imported_sum_of_ones_has_expected_statement.
Print Assumptions sum_of_ones_statement_certificate.

Definition source_sum_le_range_statement
    (f : nat -> nat) (t delta : nat) : Prop :=
  ltn (\sum_(t <= x < t + delta) f x) delta ->
  exists x, (leq t x && ltn x (t + delta)) /\ Logic.eq (f x) O.

Definition imported_finset_interval_sum
    (m n : nat) (f : nat -> nat) : Nat :=
  ImportedBigNatEq093.Finset_sum_inst3 Nat Nat
    ImportedBigNatEq093.Nat_instAddCommMonoid
    (ImportedBigNatEq093.Finset_Ico_inst1 Nat
      ImportedBigNatEq093.Nat_instPreorder
      ImportedBigNatEq093.Nat_instLocallyFiniteOrder
      (sum_nat_to_imported m) (sum_nat_to_imported n))
    (canonical_imported_function f).

Definition old_imported_list_sum
    (xs : List_inst1 Nat) : Nat :=
  ImportedBigNatEq093.List_foldr_inst3 Nat Nat Nat_add Nat_zero xs.

Definition old_imported_one : Nat :=
  ImportedBigNatEq093.OfNat_ofNat_inst1 Nat 1
    (ImportedBigNatEq093.instOfNatNat 1).

Lemma old_imported_range_succ_prop (start len step : Nat) :
  Logic.eq
    (ImportedBigNatEq093.List_range' start (Nat_succ len) step)
    (ImportedBigNatEq093.List_cons_inst1 Nat start
      (ImportedBigNatEq093.List_range' (Nat_add start step) len step)).
Proof. reflexivity. Qed.

Lemma old_imported_map_cons_prop {A B : Type} (f : A -> B) (x : A)
    (xs : ImportedBigNatEq093.List_inst1 A) :
  Logic.eq
    (ImportedBigNatEq093.List_map_inst3 A B f
      (ImportedBigNatEq093.List_cons_inst1 A x xs))
    (ImportedBigNatEq093.List_cons_inst1 B (f x)
      (ImportedBigNatEq093.List_map_inst3 A B f xs)).
Proof. reflexivity. Qed.

Lemma old_imported_foldr_cons_prop {A B : Type} (f : A -> B -> B)
    (z : B) (x : A) (xs : ImportedBigNatEq093.List_inst1 A) :
  Logic.eq
    (ImportedBigNatEq093.List_foldr_inst3 A B f z
      (ImportedBigNatEq093.List_cons_inst1 A x xs))
    (f x (ImportedBigNatEq093.List_foldr_inst3 A B f z xs)).
Proof. reflexivity. Qed.

Lemma old_imported_sub_succ_prop (a b : Nat) :
  Logic.eq
    (ImportedBigNatEq093.Nat_sub a (Nat_succ b))
    (ImportedBigNatEq093.Nat_pred
      (ImportedBigNatEq093.Nat_sub a b)).
Proof. reflexivity. Qed.

Lemma old_imported_zero_sub_prop (b : nat) :
  Logic.eq
    (ImportedBigNatEq093.Nat_sub Nat_zero (sum_nat_to_imported b))
    Nat_zero.
Proof.
  induction b as [|b IH].
  - reflexivity.
  - rewrite old_imported_sub_succ_prop IH. reflexivity.
Qed.

Lemma old_imported_succ_sub_succ_prop (a b : nat) :
  Logic.eq
    (ImportedBigNatEq093.Nat_sub
      (Nat_succ (sum_nat_to_imported a))
      (Nat_succ (sum_nat_to_imported b)))
    (ImportedBigNatEq093.Nat_sub
      (sum_nat_to_imported a) (sum_nat_to_imported b)).
Proof.
  induction b as [|b IH].
  - reflexivity.
  - rewrite !old_imported_sub_succ_prop.
    exact (f_equal ImportedBigNatEq093.Nat_pred IH).
Qed.

Lemma old_imported_sub_canonical_prop (a b : nat) :
  Logic.eq
    (ImportedBigNatEq093.Nat_sub
      (sum_nat_to_imported a) (sum_nat_to_imported b))
    (sum_nat_to_imported (a - b)).
Proof.
  induction b as [|b IH] in a |- *.
  - destruct a; reflexivity.
  - destruct a as [|a].
    + exact (old_imported_zero_sub_prop b.+1).
    + rewrite old_imported_succ_sub_succ_prop.
      exact (IH a).
Qed.

Fixpoint old_seq_nat_to_imported (xs : seq nat) :
    ImportedBigNatEq093.List_inst1 Nat :=
  match xs with
  | [::] => ImportedBigNatEq093.List_nil_inst1 Nat
  | x :: xs' => ImportedBigNatEq093.List_cons_inst1 Nat
      (sum_nat_to_imported x) (old_seq_nat_to_imported xs')
  end.

Lemma imported_finset_interval_sum_unfold_prop
    (m n : nat) (f : nat -> nat) :
  Logic.eq (imported_finset_interval_sum m n f)
    (old_imported_list_sum
      (ImportedBigNatEq093.List_map_inst3 Nat Nat
        (canonical_imported_function f)
        (ImportedBigNatEq093.List_range' (sum_nat_to_imported m)
          (Nat_sub (sum_nat_to_imported n) (sum_nat_to_imported m))
          old_imported_one))).
Proof. reflexivity. Qed.

Lemma old_imported_range_iota_prop (start len : nat) :
  Logic.eq
    (ImportedBigNatEq093.List_range'
      (sum_nat_to_imported start) (sum_nat_to_imported len) old_imported_one)
    (old_seq_nat_to_imported (iota start len)).
Proof.
  elim: len start => [|len IH] start.
  - reflexivity.
  - cbn [sum_nat_to_imported iota old_seq_nat_to_imported].
    rewrite old_imported_range_succ_prop.
    have Hstart : Logic.eq
        (Nat_add (sum_nat_to_imported start) old_imported_one)
        (sum_nat_to_imported start.+1) by reflexivity.
    rewrite Hstart (IH start.+1). reflexivity.
Qed.

Lemma old_imported_map_converted_prop (f : nat -> nat) (xs : seq nat) :
  Logic.eq
    (ImportedBigNatEq093.List_map_inst3 Nat Nat
      (canonical_imported_function f) (old_seq_nat_to_imported xs))
    (old_seq_nat_to_imported (map f xs)).
Proof.
  elim: xs => [|x xs IH].
  - reflexivity.
  - cbn [old_seq_nat_to_imported].
    rewrite old_imported_map_cons_prop.
    unfold canonical_imported_function.
    rewrite sum_rocq_roundtrip IH. reflexivity.
Qed.

Lemma old_imported_list_sum_converted_prop (xs : seq nat) :
  Logic.eq (old_imported_list_sum (old_seq_nat_to_imported xs))
    (sum_nat_to_imported (foldr addn O xs)).
Proof.
  elim: xs => [|x xs IH].
  - reflexivity.
  - cbn [old_seq_nat_to_imported foldr].
    unfold old_imported_list_sum.
    unfold old_imported_list_sum in IH.
    rewrite old_imported_foldr_cons_prop.
    rewrite IH. exact (imported_add_canonical_prop x (foldr addn O xs)).
Qed.

Lemma imported_finset_interval_sum_bridge_prop
    (m n : nat) (f : nat -> nat) :
  Logic.eq (imported_finset_interval_sum m n f)
    (sum_nat_to_imported (\sum_(m <= x < n) f x)).
Proof.
  rewrite imported_finset_interval_sum_unfold_prop.
  rewrite old_imported_sub_canonical_prop.
  rewrite old_imported_range_iota_prop.
  rewrite old_imported_map_converted_prop.
  rewrite old_imported_list_sum_converted_prop.
  rewrite /index_iota mathcomp_big_seq_as_fold.
  reflexivity.
Qed.

Definition imported_sum_range_value
    (f : nat -> nat) (t delta : nat) : Nat :=
  ImportedBigNatEq093.Finset_sum_inst3 Nat Nat
    ImportedBigNatEq093.Nat_instAddCommMonoid
    (ImportedBigNatEq093.Finset_Ico_inst1 Nat
      ImportedBigNatEq093.Nat_instPreorder
      ImportedBigNatEq093.Nat_instLocallyFiniteOrder
      (sum_nat_to_imported t)
      (Nat_add (sum_nat_to_imported t) (sum_nat_to_imported delta)))
    (canonical_imported_function f).

Definition imported_sum_le_range_statement
    (f : nat -> nat) (t delta : nat) : SProp :=
  Nat_lt (imported_sum_range_value f t delta) (sum_nat_to_imported delta) ->
  Exists Nat (fun x =>
    And (Nat_le (sum_nat_to_imported t) x)
      (And (Nat_lt x
              (Nat_add (sum_nat_to_imported t) (sum_nat_to_imported delta)))
        (eq (canonical_imported_function f x) Nat_zero))).

Definition original_sum_le_range_has_expected_statement
    (f : nat -> nat) (t delta : nat) :
    source_sum_le_range_statement f t delta :=
  @Generated_util__sum.sum_le_summation_range f t delta.

Definition imported_sum_le_range_has_expected_statement
    (f : nat -> nat) (t delta : nat) :
  imported_sum_le_range_statement f t delta :=
  ImportedBigNatEq093.Prosa_Util_Sum_sum_le_summation_range
    (canonical_imported_function f)
    (sum_nat_to_imported t) (sum_nat_to_imported delta).

Lemma imported_sum_range_value_prop
    (f : nat -> nat) (t delta : nat) :
  Logic.eq (imported_sum_range_value f t delta)
    (sum_nat_to_imported (\sum_(t <= x < t + delta) f x)).
Proof.
  unfold imported_sum_range_value.
  rewrite imported_add_canonical_prop.
  change (Logic.eq (imported_finset_interval_sum t (t + delta) f)
    (sum_nat_to_imported (\sum_(t <= x < t + delta) f x))).
  (* The old actual Finset artifact remains the semantic target for this
     theorem until its proof-field-heavy type admits the same normalization. *)
  exact (imported_finset_interval_sum_bridge_prop t (t + delta) f).
Qed.

Lemma sum_le_range_exists_backward_strict
    (f : nat -> nat) (t delta : nat)
    (H : Exists Nat (fun x =>
      And (Nat_le (sum_nat_to_imported t) x)
        (And (Nat_lt x
                (Nat_add (sum_nat_to_imported t) (sum_nat_to_imported delta)))
          (eq (canonical_imported_function f x) Nat_zero)))) :
  StrictlyInhabited
    (exists x, (leq t x && ltn x (t + delta)) /\ Logic.eq (f x) O).
Proof.
  destruct H as [xL Hparts].
  destruct Hparts as [Hlow Hrest]. destruct Hrest as [Hhigh Hzero].
  apply strictly_inhabits.
  exists (sum_imported_nat_to_rocq xL). split.
  - apply/andP. split.
    + have Hround := sum_imported_roundtrip xL.
      have HlowC := sum_eq_transport
        (fun z => Nat_le (sum_nat_to_imported t) z) _ _
        (sum_eq_sym _ _ Hround) Hlow.
      exact (interpret_strict _
        (sum_le_backward _ _ HlowC)).
    + have Hround := sum_imported_roundtrip xL.
      have HhighX := sum_eq_transport
        (fun z => Nat_lt z
          (Nat_add (sum_nat_to_imported t) (sum_nat_to_imported delta)))
        _ _ (sum_eq_sym _ _ Hround) Hhigh.
      have HhighC := sum_eq_transport
        (fun z => Nat_lt
          (sum_nat_to_imported (sum_imported_nat_to_rocq xL)) z)
        _ _ (imported_add_canonical t delta) HhighX.
      exact (interpret_strict _
        (sum_lt_backward _ _ HhighC)).
  - unfold canonical_imported_function in Hzero.
    have Hdecoded := interpret_strict _
      (sum_decode_zero_strict _ Hzero).
    exact Hdecoded.
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

Theorem sum_le_summation_range_statement_certificate
    (f : nat -> nat) (t delta : nat) :
  PropSPropRel
    (source_sum_le_range_statement f t delta)
    (imported_sum_le_range_statement f t delta).
Proof.
  apply prop_sprop_rel_intro.
  - intro Hsource. intro HltL.
    have Hvalue := coq_eq_to_imported_eq _ _
      (imported_sum_range_value_prop f t delta).
    have HltC := sum_eq_transport
      (fun z => Nat_lt z (sum_nat_to_imported delta)) _ _ Hvalue HltL.
    have HltR := interpret_strict _
      (sum_lt_backward _ _ HltC).
    have HexR := Hsource HltR.
    destruct (embed_exists nat
      (fun x => (leq t x && ltn x (t + delta)) /\ Logic.eq (f x) O)
      HexR) as [x Hx].
    apply (Exists_intro Nat _ (sum_nat_to_imported x)).
    apply (And_intro _ _ (sum_le_forward _ _
      (sum_and_left _ _ (Logic.proj1 Hx)))).
    apply (And_intro _ _).
    + exact (sum_eq_transport
        (fun z => Nat_lt (sum_nat_to_imported x) z) _ _
        (sum_eq_sym _ _ (imported_add_canonical t delta))
        (sum_lt_forward _ _ (sum_and_right _ _ (Logic.proj1 Hx)))).
    + unfold canonical_imported_function.
      rewrite sum_rocq_roundtrip (Logic.proj2 Hx).
      exact (eq_refl Nat_zero).
  - intro Htarget. apply strictly_inhabits. intro HltR.
    have Hvalue := coq_eq_to_imported_eq _ _
      (imported_sum_range_value_prop f t delta).
    have HltC := sum_lt_forward _ _ HltR.
    have HltL := sum_eq_transport
      (fun z => Nat_lt z (sum_nat_to_imported delta)) _ _
      (sum_eq_sym _ _ Hvalue) HltC.
    exact (interpret_strict _
      (sum_le_range_exists_backward_strict f t delta (Htarget HltL))).
Qed.

Print Assumptions original_sum_le_range_has_expected_statement.
Print Assumptions imported_sum_le_range_has_expected_statement.
Print Assumptions sum_le_summation_range_statement_certificate.
