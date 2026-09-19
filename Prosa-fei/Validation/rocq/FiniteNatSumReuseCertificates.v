From mathcomp Require Import ssreflect ssrbool ssrnat seq bigop.
From LeanImport Require Import Lean.
Require Import ImportedBigNatEq093 PropSPropBridge HardSumCertificate
  FiniteNatSumBridge.
From HardSource Require Import Generated_util__sum.

Definition source_sum_of_ones_statement (t delta : nat) : Prop :=
  Logic.eq (\sum_(t <= x < t + delta) 1) delta.

Definition imported_sum_of_ones_value (t delta : nat) : Nat :=
  Finset_sum_inst3 Nat Nat Nat_instAddCommMonoid
    (Finset_Ico_inst1 Nat Nat_instPreorder Nat_instLocallyFiniteOrder
      (sum_nat_to_imported t)
      (Nat_add (sum_nat_to_imported t) (sum_nat_to_imported delta)))
    (fun _ : Nat => imported_one).

Definition imported_sum_of_ones_statement (t delta : nat) : SProp :=
  eq (imported_sum_of_ones_value t delta) (sum_nat_to_imported delta).

Definition original_sum_of_ones_has_expected_statement (t delta : nat) :
    source_sum_of_ones_statement t delta :=
  @Generated_util__sum.sum_of_ones t delta.

Definition imported_sum_of_ones_has_expected_statement (t delta : nat) :
    imported_sum_of_ones_statement t delta :=
  Prosa_Util_Sum_sum_of_ones
    (sum_nat_to_imported t) (sum_nat_to_imported delta).

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
    apply prop_sprop_trusted_eq_intro.
    rewrite imported_sum_of_ones_value_prop Hsource. reflexivity.
  - intro Htarget. apply strictly_inhabits.
    have HtargetP := prop_sprop_trusted_elim _
      (sprop_eq_to_strict_eq _ _ Htarget).
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

Definition imported_sum_range_value
    (f : nat -> nat) (t delta : nat) : Nat :=
  Finset_sum_inst3 Nat Nat Nat_instAddCommMonoid
    (Finset_Ico_inst1 Nat Nat_instPreorder Nat_instLocallyFiniteOrder
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
  Prosa_Util_Sum_sum_le_summation_range
    (canonical_imported_function f)
    (sum_nat_to_imported t) (sum_nat_to_imported delta).

Lemma imported_sum_range_value_prop
    (f : nat -> nat) (t delta : nat) :
  Logic.eq (imported_sum_range_value f t delta)
    (sum_nat_to_imported (\sum_(t <= x < t + delta) f x)).
Proof.
  unfold imported_sum_range_value.
  rewrite imported_add_canonical_prop.
  change (Logic.eq
    (imported_interval_sum t (t + delta) f)
    (sum_nat_to_imported (\sum_(t <= x < t + delta) f x))).
  exact (finite_nat_sum_value_bridge_prop t (t + delta) f).
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
      exact (prop_sprop_trusted_elim _
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
      exact (prop_sprop_trusted_elim _
        (sum_lt_backward _ _ HhighC)).
  - unfold canonical_imported_function in Hzero.
    have Hdecoded := prop_sprop_trusted_elim _
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
    have Hvalue := prop_sprop_trusted_eq_intro Nat _ _
      (imported_sum_range_value_prop f t delta).
    have HltC := sum_eq_transport
      (fun z => Nat_lt z (sum_nat_to_imported delta)) _ _ Hvalue HltL.
    have HltR := prop_sprop_trusted_elim _
      (sum_lt_backward _ _ HltC).
    have HexR := Hsource HltR.
    destruct (prop_sprop_trusted_exists_intro nat
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
    have Hvalue := prop_sprop_trusted_eq_intro Nat _ _
      (imported_sum_range_value_prop f t delta).
    have HltC := sum_lt_forward _ _ HltR.
    have HltL := sum_eq_transport
      (fun z => Nat_lt z (sum_nat_to_imported delta)) _ _
      (sum_eq_sym _ _ Hvalue) HltC.
    exact (prop_sprop_trusted_elim _
      (sum_le_range_exists_backward_strict f t delta (Htarget HltL))).
Qed.

Print Assumptions original_sum_le_range_has_expected_statement.
Print Assumptions imported_sum_le_range_has_expected_statement.
Print Assumptions sum_le_summation_range_statement_certificate.
