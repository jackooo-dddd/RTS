From mathcomp Require Import ssreflect ssrbool ssrnat bigop.
From LeanImport Require Import Lean.
Require Import ImportedBigNatEq093 PropSPropBridge.
From HardSource Require Import Generated_util__sum.

Inductive Sum_STrue : SProp := sum_sI.
Inductive Sum_SFalse : SProp := .

Definition sum_false_elim (P : SProp) (H : Sum_SFalse) : P :=
  match H return P with end.

Fixpoint sum_nat_to_imported (n : nat) : Nat :=
  match n with O => Nat_zero | S n' => Nat_succ (sum_nat_to_imported n') end.

Fixpoint sum_imported_nat_to_rocq (n : Nat) : nat :=
  match n with Nat_zero => O | Nat_succ n' => S (sum_imported_nat_to_rocq n') end.

Definition sum_eq_sym {A : Type} (x y : A) : eq x y -> eq y x :=
  fun H => match H in eq _ z return eq z x with eq_refl => eq_refl x end.

Definition sum_eq_trans {A : Type} (x y z : A) :
    eq x y -> eq y z -> eq x z :=
  fun Hxy Hyz => match Hxy in eq _ y0 return eq y0 z -> eq x z with
                 | eq_refl => fun H => H
                 end Hyz.

Definition sum_eq_transport {A : Type} (P : A -> SProp) (x y : A) :
    eq x y -> P x -> P y :=
  fun H px => match H in eq _ z return P z with eq_refl => px end.

Definition sum_succ_ne_zero (n : Nat) : eq (Nat_succ n) Nat_zero -> Sum_SFalse :=
  fun H => match H in eq _ z return
    match z with Nat_zero => Sum_SFalse | Nat_succ _ => Sum_STrue end
  with eq_refl => sum_sI end.

Definition sum_decode_zero_strict (n : nat) :
    eq (sum_nat_to_imported n) Nat_zero -> StrictlyInhabited (Logic.eq n O) :=
  match n return eq (sum_nat_to_imported n) Nat_zero ->
      StrictlyInhabited (Logic.eq n O)
  with
  | O => fun _ => strictly_inhabits (Logic.eq_refl O)
  | S n' => fun H => sum_false_elim _ (sum_succ_ne_zero _ H)
  end.

Fixpoint sum_imported_roundtrip (n : Nat) :
    eq (sum_nat_to_imported (sum_imported_nat_to_rocq n)) n :=
  match n with
  | Nat_zero => eq_refl Nat_zero
  | Nat_succ n' =>
      match sum_imported_roundtrip n' in eq _ z return
        eq (Nat_succ (sum_nat_to_imported (sum_imported_nat_to_rocq n')))
           (Nat_succ z)
      with eq_refl => eq_refl _ end
  end.

Lemma sum_rocq_roundtrip (n : nat) :
  Logic.eq (sum_imported_nat_to_rocq (sum_nat_to_imported n)) n.
Proof. induction n; cbn; first reflexivity. f_equal. exact IHn. Qed.

Fixpoint sum_zero_le (m : Nat) : Nat_le Nat_zero m :=
  match m with
  | Nat_zero => Lean.Nat_le_refl Nat_zero
  | Nat_succ m' => Lean.Nat_le_step Nat_zero m' (sum_zero_le m')
  end.

Fixpoint sum_le_succ_succ (n m : Nat) (H : Nat_le n m) :
    Nat_le (Nat_succ n) (Nat_succ m) :=
  match H with
  | Lean.Nat_le_refl => Lean.Nat_le_refl _
  | Lean.Nat_le_step k H' => Lean.Nat_le_step _ _ (sum_le_succ_succ n k H')
  end.

Fixpoint sum_le_left_pred (n m : Nat) (H : Nat_le (Nat_succ n) m) : Nat_le n m :=
  match H with
  | Lean.Nat_le_refl => Lean.Nat_le_step n n (Lean.Nat_le_refl n)
  | Lean.Nat_le_step k H' => Lean.Nat_le_step n k (sum_le_left_pred n k H')
  end.

Definition sum_le_succ_inv (n m : Nat)
    (H : Nat_le (Nat_succ n) (Nat_succ m)) : Nat_le n m :=
  match H in Nat_le _ z return
    match z with Nat_zero => Sum_STrue | Nat_succ k => Nat_le n k end
  with
  | Lean.Nat_le_refl => Lean.Nat_le_refl n
  | Lean.Nat_le_step k H' => sum_le_left_pred n k H'
  end.

Definition sum_succ_not_le_zero (n : Nat)
    (H : Nat_le (Nat_succ n) Nat_zero) : Sum_SFalse :=
  match H in Nat_le _ z return
    match z with Nat_zero => Sum_SFalse | Nat_succ _ => Sum_STrue end
  with
  | Lean.Nat_le_refl => sum_sI
  | Lean.Nat_le_step _ _ => sum_sI
  end.

Fixpoint sum_le_forward (n m : nat) : is_true (leq n m) ->
    Nat_le (sum_nat_to_imported n) (sum_nat_to_imported m) :=
  match n, m return is_true (leq n m) ->
      Nat_le (sum_nat_to_imported n) (sum_nat_to_imported m)
  with
  | O, m' => fun _ => sum_zero_le _
  | S n', O => fun H => sum_false_elim _
      (match H in Logic.eq _ z return
         match z with false => Sum_STrue | true => Sum_SFalse end
       with Logic.eq_refl => sum_sI end)
  | S n', S m' => fun H => sum_le_succ_succ _ _ (sum_le_forward n' m' H)
  end.

Fixpoint sum_le_backward (n m : nat) :
    Nat_le (sum_nat_to_imported n) (sum_nat_to_imported m) ->
    StrictlyInhabited (is_true (leq n m)) :=
  match n, m return Nat_le (sum_nat_to_imported n) (sum_nat_to_imported m) ->
      StrictlyInhabited (is_true (leq n m))
  with
  | O, _ => fun _ => strictly_inhabits (Logic.eq_refl true)
  | S n', O => fun H => sum_false_elim _ (sum_succ_not_le_zero _ H)
  | S n', S m' => fun H => sum_le_backward n' m' (sum_le_succ_inv _ _ H)
  end.

Definition sum_lt_forward n m : is_true (ltn n m) ->
    Nat_lt (sum_nat_to_imported n) (sum_nat_to_imported m) :=
  sum_le_forward n.+1 m.

Definition sum_lt_backward n m :
    Nat_lt (sum_nat_to_imported n) (sum_nat_to_imported m) ->
    StrictlyInhabited (is_true (ltn n m)) :=
  sum_le_backward n.+1 m.

Definition canonical_imported_function (F : nat -> nat) : Nat -> Nat :=
  fun n => sum_nat_to_imported (F (sum_imported_nat_to_rocq n)).

Definition source_big_nat_eq0_statement (m n : nat) (F : nat -> nat) : Prop :=
  Logic.eq (\sum_(m <= i < n) F i) O <->
  forall i, leq m i && ltn i n -> Logic.eq (F i) O.

Definition imported_interval_sum (m n : nat) (F : nat -> nat) : Nat :=
  Finset_sum_inst3 Nat Nat Nat_instAddCommMonoid
    (Finset_Ico_inst1 Nat Nat_instPreorder Nat_instLocallyFiniteOrder
      (sum_nat_to_imported m) (sum_nat_to_imported n))
    (canonical_imported_function F).

Definition imported_big_nat_eq0_statement (m n : nat) (F : nat -> nat) : SProp :=
  Iff
    (eq (imported_interval_sum m n F) Nat_zero)
    (forall i : Nat,
      And (Nat_le (sum_nat_to_imported m) i)
          (Nat_lt i (sum_nat_to_imported n)) ->
      eq (canonical_imported_function F i) Nat_zero).

Definition original_big_nat_eq0_has_expected_statement
    (m n : nat) (F : nat -> nat) :
    source_big_nat_eq0_statement m n F :=
  @Generated_util__sum.big_nat_eq0 m n F.

Definition imported_big_nat_eq0_has_expected_statement
    (m n : nat) (F : nat -> nat) :
    imported_big_nat_eq0_statement m n F :=
  Prosa_Util_Sum_big_nat_eq0
    (sum_nat_to_imported m) (sum_nat_to_imported n)
    (canonical_imported_function F).

(** The sole open semantic dependency: equality of the two interval-sum
    values.  It names the actual imported [Finset.sum (Finset.Ico ...)] body,
    not a replacement model. *)
Definition FiniteNatSumValueBridge (m n : nat) (F : nat -> nat) : SProp :=
  eq (imported_interval_sum m n F)
     (sum_nat_to_imported (\sum_(m <= i < n) F i)).

Definition sum_value_zero_forward (m n : nat) (F : nat -> nat)
    (Hsum : FiniteNatSumValueBridge m n F)
    (Hzero : Logic.eq (\sum_(m <= i < n) F i) O) :
    eq (imported_interval_sum m n F) Nat_zero :=
  match Hzero in Logic.eq _ z return
    eq (imported_interval_sum m n F) (sum_nat_to_imported z)
  with
  | Logic.eq_refl => Hsum
  end.

Lemma sum_pointwise_forward (m n : nat) (F : nat -> nat)
    (Hall : forall i, leq m i && ltn i n -> Logic.eq (F i) O) :
  forall i : Nat,
    And (Nat_le (sum_nat_to_imported m) i)
        (Nat_lt i (sum_nat_to_imported n)) ->
    eq (canonical_imported_function F i) Nat_zero.
Proof.
  intros i Hbounds. destruct Hbounds as [Hlow Hhigh].
  have Hround := sum_imported_roundtrip i.
  have HlowC := sum_eq_transport
    (fun z => Nat_le (sum_nat_to_imported m) z) _ _
    (sum_eq_sym _ _ Hround) Hlow.
  have HhighC := sum_eq_transport
    (fun z => Nat_lt z (sum_nat_to_imported n)) _ _
    (sum_eq_sym _ _ Hround) Hhigh.
  have Hi := Hall (sum_imported_nat_to_rocq i).
  have Hi0 : Logic.eq (F (sum_imported_nat_to_rocq i)) O.
  { apply Hi. apply/andP. split.
    - exact (prop_sprop_trusted_elim _ (sum_le_backward _ _ HlowC)).
    - exact (prop_sprop_trusted_elim _ (sum_lt_backward _ _ HhighC)). }
  unfold canonical_imported_function. rewrite Hi0. exact (eq_refl Nat_zero).
Qed.

Lemma sum_target_zero_to_source_point_strict (m n : nat) (F : nat -> nat)
    (Hsum : FiniteNatSumValueBridge m n F)
    (Hzero : eq (imported_interval_sum m n F) Nat_zero ->
      forall i : Nat,
        And (Nat_le (sum_nat_to_imported m) i)
            (Nat_lt i (sum_nat_to_imported n)) ->
        eq (canonical_imported_function F i) Nat_zero)
    (HsourceZero : Logic.eq (\sum_(m <= i < n) F i) O) :
  StrictlyInhabited
    (forall i, leq m i && ltn i n -> Logic.eq (F i) O).
Proof.
  apply strictly_inhabits. intros i Hi. move/andP: Hi => [Hlow Hhigh].
  have Hdecoded := prop_sprop_trusted_elim _
    (sum_decode_zero_strict _
      (Hzero (sum_value_zero_forward m n F Hsum HsourceZero)
        (sum_nat_to_imported i)
        (And_intro _ _ (sum_le_forward _ _ Hlow)
          (sum_lt_forward _ _ Hhigh)))).
  rewrite sum_rocq_roundtrip in Hdecoded. exact Hdecoded.
Qed.

Lemma sum_target_point_to_source_zero_strict (m n : nat) (F : nat -> nat)
    (Hsum : FiniteNatSumValueBridge m n F)
    (Hpoint : (forall i : Nat,
      And (Nat_le (sum_nat_to_imported m) i)
          (Nat_lt i (sum_nat_to_imported n)) ->
      eq (canonical_imported_function F i) Nat_zero) ->
      eq (imported_interval_sum m n F) Nat_zero)
    (Hall : forall i, leq m i && ltn i n -> Logic.eq (F i) O) :
  StrictlyInhabited (Logic.eq (\sum_(m <= i < n) F i) O).
Proof.
  have Hcanonical := sum_eq_trans _ _ _ (sum_eq_sym _ _ Hsum)
    (Hpoint (sum_pointwise_forward m n F Hall)).
  exact (sum_decode_zero_strict _ Hcanonical).
Qed.

Theorem big_nat_eq0_parametric_certificate
    (m n : nat) (F : nat -> nat)
    (Hsum : FiniteNatSumValueBridge m n F) :
  PropSPropRel
    (source_big_nat_eq0_statement m n F)
    (imported_big_nat_eq0_statement m n F).
Proof.
  unfold FiniteNatSumValueBridge in Hsum.
  apply prop_sprop_rel_intro.
  - intro Hsource. destruct Hsource as [Hzero Hpoint].
    apply (Iff_intro _ _).
    + intro HsumZero.
      have Hcanonical := sum_eq_trans _ _ _
        (sum_eq_sym _ _ Hsum) HsumZero.
      have HsourceZero := prop_sprop_trusted_elim _
        (sum_decode_zero_strict _ Hcanonical).
      intros i Hbounds. destruct Hbounds as [Hlow Hhigh].
      have Hround := sum_imported_roundtrip i.
      have HlowC := sum_eq_transport
        (fun z => Nat_le (sum_nat_to_imported m) z) _ _
        (sum_eq_sym _ _ Hround) Hlow.
      have HhighC := sum_eq_transport
        (fun z => Nat_lt z (sum_nat_to_imported n)) _ _
        (sum_eq_sym _ _ Hround) Hhigh.
      have HiZero := Hzero HsourceZero (sum_imported_nat_to_rocq i).
      have HiZero' : Logic.eq (F (sum_imported_nat_to_rocq i)) O.
      { apply HiZero. apply/andP. split.
        - exact (prop_sprop_trusted_elim _ (sum_le_backward _ _ HlowC)).
        - exact (prop_sprop_trusted_elim _ (sum_lt_backward _ _ HhighC)). }
      unfold canonical_imported_function. rewrite HiZero'. exact (eq_refl Nat_zero).
    + intro Hall.
      have HsourceZero : Logic.eq (\sum_(m <= i < n) F i) O.
      { apply Hpoint. intros i Hi. move/andP: Hi => [Hlow Hhigh].
        have Heq := Hall (sum_nat_to_imported i)
          (And_intro _ _ (sum_le_forward _ _ Hlow) (sum_lt_forward _ _ Hhigh)).
        have Hdecoded := prop_sprop_trusted_elim _
          (sum_decode_zero_strict _ Heq).
        rewrite sum_rocq_roundtrip in Hdecoded. exact Hdecoded. }
      rewrite HsourceZero in Hsum. exact Hsum.
  - intro Htarget. destruct Htarget as [Hzero Hpoint].
    apply strictly_inhabits. split.
    + intro HsumZero.
      exact (prop_sprop_trusted_elim _
        (sum_target_zero_to_source_point_strict m n F Hsum Hzero HsumZero)).
    + intro Hall.
      exact (prop_sprop_trusted_elim _
        (sum_target_point_to_source_zero_strict m n F Hsum Hpoint Hall)).
Qed.

Print Assumptions big_nat_eq0_parametric_certificate.
Print Assumptions original_big_nat_eq0_has_expected_statement.
Print Assumptions imported_big_nat_eq0_has_expected_statement.
