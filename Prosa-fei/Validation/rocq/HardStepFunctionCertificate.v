From mathcomp Require Import ssreflect ssrbool ssrnat.
From LeanImport Require Import Lean.
Require Import ImportedExistsFirstIntermediatePoint93.
Require Import PropSPropBridge.
From HardSource Require Import Generated_util__unit_growth.

Inductive Step_STrue : SProp := step_sI.
Inductive Step_SFalse : SProp := .

Definition step_false_elim (P : SProp) (H : Step_SFalse) : P :=
  match H return P with end.

Definition step_imported_false_elim (P : SProp) (H : False) : P :=
  match H return P with end.

Fixpoint step_nat_to_imported (n : nat) : Nat :=
  match n with
  | O => Nat_zero
  | S n' => Nat_succ (step_nat_to_imported n')
  end.

Fixpoint step_imported_nat_to_rocq (n : Nat) : nat :=
  match n with
  | Nat_zero => O
  | Nat_succ n' => S (step_imported_nat_to_rocq n')
  end.

Definition StepNatRel (nR : nat) (nL : Nat) : SProp :=
  eq (step_nat_to_imported nR) nL.

Definition step_nat_succ_congr (a b : Nat) :
    eq a b -> eq (Nat_succ a) (Nat_succ b) :=
  fun H => match H in eq _ z return eq (Nat_succ a) (Nat_succ z) with
           | eq_refl => eq_refl (Nat_succ a)
           end.

Fixpoint step_imported_nat_roundtrip (n : Nat) :
    eq (step_nat_to_imported (step_imported_nat_to_rocq n)) n :=
  match n with
  | Nat_zero => eq_refl Nat_zero
  | Nat_succ n' =>
      step_nat_succ_congr _ _ (step_imported_nat_roundtrip n')
  end.

Inductive StepBoolRel : bool -> Bool -> SProp :=
| step_bool_false : StepBoolRel false Bool_false
| step_bool_true : StepBoolRel true Bool_true.

Definition StepPredRel (PR : nat -> bool) (PL : Nat -> Bool) : SProp :=
  forall nR nL, StepNatRel nR nL -> StepBoolRel (PR nR) (PL nL).

Definition step_imported_eq_transport {A : Type} (P : A -> SProp)
    (x y : A) : eq x y -> P x -> P y :=
  fun H px => match H in eq _ z return P z with
              | eq_refl => px
              end.

Definition step_imported_eq_sym {A : Type} (x y : A) :
    eq x y -> eq y x :=
  fun H => match H in eq _ z return eq z x with
           | eq_refl => eq_refl x
           end.

Definition step_bool_false_ne_true : eq Bool_false Bool_true -> False :=
  fun H => match H in eq _ z return
    match z with Bool_false => Step_STrue | Bool_true => False end
  with eq_refl => step_sI end.

Definition step_bool_truth_forward bR bL :
    StepBoolRel bR bL -> is_true bR -> eq bL Bool_true :=
  fun Hrel =>
    match Hrel in StepBoolRel bR0 bL0 return
      is_true bR0 -> eq bL0 Bool_true
    with
    | step_bool_false => fun H => step_false_elim _
        (match H in Logic.eq _ z return
           match z with false => Step_STrue | true => Step_SFalse end
         with Logic.eq_refl => step_sI end)
    | step_bool_true => fun _ => eq_refl Bool_true
    end.

Definition step_bool_truth_backward_strict bR bL :
    StepBoolRel bR bL -> eq bL Bool_true ->
    StrictlyInhabited (is_true bR) :=
  fun Hrel =>
    match Hrel in StepBoolRel bR0 bL0 return
      eq bL0 Bool_true -> StrictlyInhabited (is_true bR0)
    with
    | step_bool_false => fun H =>
        step_imported_false_elim _ (step_bool_false_ne_true H)
    | step_bool_true => fun _ =>
        strictly_inhabits (Logic.eq_refl true)
    end.

Definition step_bool_neg_forward bR bL :
    StepBoolRel bR bL -> is_true (~~ bR) -> Not (eq bL Bool_true) :=
  fun Hrel =>
    match Hrel in StepBoolRel bR0 bL0 return
      is_true (~~ bR0) -> Not (eq bL0 Bool_true)
    with
    | step_bool_false => fun _ H => step_bool_false_ne_true H
    | step_bool_true => fun H _ => step_false_elim _
        (match H in Logic.eq _ z return
           match z with false => Step_STrue | true => Step_SFalse end
         with Logic.eq_refl => step_sI end)
    end.

Definition step_bool_neg_backward_strict bR bL :
    StepBoolRel bR bL -> Not (eq bL Bool_true) ->
    StrictlyInhabited (is_true (~~ bR)) :=
  fun Hrel =>
    match Hrel in StepBoolRel bR0 bL0 return
      Not (eq bL0 Bool_true) -> StrictlyInhabited (is_true (~~ bR0))
    with
    | step_bool_false => fun _ =>
        strictly_inhabits (Logic.eq_refl true)
    | step_bool_true => fun H =>
        step_imported_false_elim _ (H (eq_refl Bool_true))
    end.

Definition step_and_left (a b : bool) :
    is_true (a && b) -> is_true a :=
  match a, b return is_true (a && b) -> is_true a with
  | true, true => fun _ => Logic.eq_refl true
  | true, false => fun _ => Logic.eq_refl true
  | false, true => fun H => H
  | false, false => fun H => H
  end.

Definition step_and_right (a b : bool) :
    is_true (a && b) -> is_true b :=
  match a, b return is_true (a && b) -> is_true b with
  | true, true => fun _ => Logic.eq_refl true
  | true, false => fun H => H
  | false, true => fun _ => Logic.eq_refl true
  | false, false => fun H => H
  end.

Fixpoint step_zero_le (m : Nat) : Nat_le Nat_zero m :=
  match m with
  | Nat_zero => Lean.Nat_le_refl Nat_zero
  | Nat_succ m' => Lean.Nat_le_step Nat_zero m' (step_zero_le m')
  end.

Fixpoint step_le_succ_succ (n m : Nat) (H : Nat_le n m) :
    Nat_le (Nat_succ n) (Nat_succ m) :=
  match H with
  | Lean.Nat_le_refl => Lean.Nat_le_refl (Nat_succ n)
  | Lean.Nat_le_step k H' =>
      Lean.Nat_le_step (Nat_succ n) (Nat_succ k)
        (step_le_succ_succ n k H')
  end.

Fixpoint step_le_left_pred (n m : Nat) (H : Nat_le (Nat_succ n) m) :
    Nat_le n m :=
  match H with
  | Lean.Nat_le_refl => Lean.Nat_le_step n n (Lean.Nat_le_refl n)
  | Lean.Nat_le_step k H' =>
      Lean.Nat_le_step n k (step_le_left_pred n k H')
  end.

Definition step_le_succ_inv (n m : Nat)
    (H : Nat_le (Nat_succ n) (Nat_succ m)) : Nat_le n m :=
  match H in Nat_le _ z return
    match z with Nat_zero => Step_STrue | Nat_succ k => Nat_le n k end
  with
  | Lean.Nat_le_refl => Lean.Nat_le_refl n
  | Lean.Nat_le_step k H' => step_le_left_pred n k H'
  end.

Definition step_succ_not_le_zero (n : Nat)
    (H : Nat_le (Nat_succ n) Nat_zero) : Step_SFalse :=
  match H in Nat_le _ z return
    match z with Nat_zero => Step_SFalse | Nat_succ _ => Step_STrue end
  with
  | Lean.Nat_le_refl => step_sI
  | Lean.Nat_le_step _ _ => step_sI
  end.

Fixpoint step_le_forward (n m : nat) :
    is_true (leq n m) ->
    Nat_le (step_nat_to_imported n) (step_nat_to_imported m) :=
  match n, m return is_true (leq n m) ->
      Nat_le (step_nat_to_imported n) (step_nat_to_imported m)
  with
  | O, m' => fun _ => step_zero_le (step_nat_to_imported m')
  | S n', O => fun H => step_false_elim _
      (match H in Logic.eq _ z return
         match z with false => Step_STrue | true => Step_SFalse end
       with Logic.eq_refl => step_sI end)
  | S n', S m' => fun H => step_le_succ_succ _ _ (step_le_forward n' m' H)
  end.

Fixpoint step_le_backward_strict (n m : nat) :
    Nat_le (step_nat_to_imported n) (step_nat_to_imported m) ->
    StrictlyInhabited (is_true (leq n m)) :=
  match n, m return
    Nat_le (step_nat_to_imported n) (step_nat_to_imported m) ->
    StrictlyInhabited (is_true (leq n m))
  with
  | O, _ => fun _ => strictly_inhabits (Logic.eq_refl true)
  | S n', O => fun H => step_false_elim _
      (step_succ_not_le_zero (step_nat_to_imported n') H)
  | S n', S m' => fun H =>
      step_le_backward_strict n' m' (step_le_succ_inv _ _ H)
  end.

Definition step_lt_forward (n m : nat) :
    is_true (ltn n m) ->
    Nat_lt (step_nat_to_imported n) (step_nat_to_imported m) :=
  step_le_forward n.+1 m.

Definition step_lt_backward_strict (n m : nat) :
    Nat_lt (step_nat_to_imported n) (step_nat_to_imported m) ->
    StrictlyInhabited (is_true (ltn n m)) :=
  step_le_backward_strict n.+1 m.

Definition source_exists_first_statement
    (P : nat -> bool) (t1 t2 : nat) : Prop :=
  leq t1 t2 -> ~~ P t1 -> P t2 ->
  exists t, (ltn t1 t && leq t t2) /\
    (forall x, leq t1 x && ltn x t -> ~~ P x) /\ P t.

Definition imported_exists_first_statement
    (P : Nat -> Bool) (t1 t2 : Nat) : SProp :=
  LE_le_inst1 Nat instLENat t1 t2 ->
  Not (eq (P t1) Bool_true) ->
  eq (P t2) Bool_true ->
  Exists Nat (fun t =>
    And (And (LT_lt_inst1 Nat instLTNat t1 t)
             (LE_le_inst1 Nat instLENat t t2))
        (And
          (forall x,
            And (LE_le_inst1 Nat instLENat t1 x)
                (LT_lt_inst1 Nat instLTNat x t) ->
            Not (eq (P x) Bool_true))
          (eq (P t) Bool_true))).

Definition original_exists_first_has_expected_statement
    (P : nat -> bool) (t1 t2 : nat) :
    source_exists_first_statement P t1 t2 :=
  @Generated_util__unit_growth.exists_first_intermediate_point
    P t1 t2.

Definition imported_exists_first_has_expected_statement
    (P : Nat -> Bool) (t1 t2 : Nat) :
    imported_exists_first_statement P t1 t2 :=
  Prosa_Util_Step_function_StepFunction_exists_first_intermediate_point
    P t1 t2.

Lemma step_result_backward_strict
    (PR : nat -> bool) (PL : Nat -> Bool) (t1 t2 : nat)
    (Hpred : StepPredRel PR PL)
    (Hresult : Exists Nat (fun t =>
      And (And (Nat_lt (step_nat_to_imported t1) t)
               (Nat_le t (step_nat_to_imported t2)))
          (And
            (forall x,
              And (Nat_le (step_nat_to_imported t1) x) (Nat_lt x t) ->
              Not (eq (PL x) Bool_true))
            (eq (PL t) Bool_true)))) :
  StrictlyInhabited
    (exists t, (ltn t1 t && leq t t2) /\
      (forall x, leq t1 x && ltn x t -> ~~ PR x) /\ PR t).
Proof.
  destruct Hresult as [tL Hparts].
  destruct Hparts as [Hbounds Hrest].
  destruct Hbounds as [HltL HleL].
  destruct Hrest as [HallL HPtL].
  apply strictly_inhabits.
  exists (step_imported_nat_to_rocq tL).
  split.
  - apply/andP. split.
    + exact (prop_sprop_trusted_elim _
        (step_lt_backward_strict t1 (step_imported_nat_to_rocq tL)
          (step_imported_eq_transport
            (fun z => Nat_lt (step_nat_to_imported t1) z)
            tL (step_nat_to_imported (step_imported_nat_to_rocq tL))
            (step_imported_eq_sym _ _ (step_imported_nat_roundtrip tL))
            HltL))).
    + exact (prop_sprop_trusted_elim _
        (step_le_backward_strict (step_imported_nat_to_rocq tL) t2
          (step_imported_eq_transport
            (fun z => Nat_le z (step_nat_to_imported t2))
            tL (step_nat_to_imported (step_imported_nat_to_rocq tL))
            (step_imported_eq_sym _ _ (step_imported_nat_roundtrip tL))
            HleL))).
  - split.
    + intros x Hx. move/andP: Hx => [HlowR HhighR].
      have HhighL0 := step_lt_forward x (step_imported_nat_to_rocq tL)
        HhighR.
      have HhighL := step_imported_eq_transport
        (fun z => Nat_lt (step_nat_to_imported x) z)
        (step_nat_to_imported (step_imported_nat_to_rocq tL)) tL
        (step_imported_nat_roundtrip tL) HhighL0.
      have HnotL := HallL (step_nat_to_imported x)
        (And_intro _ _ (step_le_forward t1 x HlowR) HhighL).
      have Hpx := Hpred x (step_nat_to_imported x) (eq_refl _).
      exact (prop_sprop_trusted_elim _
        (step_bool_neg_backward_strict _ _ Hpx HnotL)).
    + have Hpt := Hpred (step_imported_nat_to_rocq tL) tL
        (step_imported_nat_roundtrip tL).
      exact (prop_sprop_trusted_elim _
        (step_bool_truth_backward_strict _ _ Hpt HPtL)).
Qed.

Theorem exists_first_intermediate_point_statement_certificate
    (PR : nat -> bool) (PL : Nat -> Bool)
    (t1 t2 : nat) (Hpred : StepPredRel PR PL) :
  PropSPropRel
    (source_exists_first_statement PR t1 t2)
    (imported_exists_first_statement PL
      (step_nat_to_imported t1) (step_nat_to_imported t2)).
Proof.
  apply prop_sprop_rel_intro.
  - intros Hsource HleL HnotL HtrueL.
    have HleR := prop_sprop_trusted_elim _
      (step_le_backward_strict t1 t2 HleL).
    have Hpred1 := Hpred t1 (step_nat_to_imported t1)
      (eq_refl (step_nat_to_imported t1)).
    have Hpred2 := Hpred t2 (step_nat_to_imported t2)
      (eq_refl (step_nat_to_imported t2)).
    have HnotR := prop_sprop_trusted_elim _
      (step_bool_neg_backward_strict _ _ Hpred1 HnotL).
    have HtrueR := prop_sprop_trusted_elim _
      (step_bool_truth_backward_strict _ _ Hpred2 HtrueL).
    have HsourceResult := Hsource HleR HnotR HtrueR.
    destruct (prop_sprop_trusted_exists_intro nat
      (fun t => (ltn t1 t && leq t t2) /\
        (forall x, leq t1 x && ltn x t -> ~~ PR x) /\ PR t)
      HsourceResult) as [t Hparts].
    apply (Exists_intro Nat _ (step_nat_to_imported t)).
    apply (And_intro _ _).
    + exact (And_intro _ _
        (step_lt_forward t1 t
          (step_and_left _ _ (Logic.proj1 Hparts)))
        (step_le_forward t t2
          (step_and_right _ _ (Logic.proj1 Hparts)))).
    + apply (And_intro _ _).
      * intros xL HxBounds. destruct HxBounds as [Hlow Hhigh].
        have Hround := step_imported_nat_roundtrip xL.
        have HlowC := step_imported_eq_transport
          (fun z => Nat_le (step_nat_to_imported t1) z)
          xL (step_nat_to_imported (step_imported_nat_to_rocq xL))
          (step_imported_eq_sym _ _ Hround) Hlow.
        have HhighC := step_imported_eq_transport
          (fun z => Nat_lt z (step_nat_to_imported t))
          xL (step_nat_to_imported (step_imported_nat_to_rocq xL))
          (step_imported_eq_sym _ _ Hround) Hhigh.
        have HlowR := prop_sprop_trusted_elim _
          (step_le_backward_strict t1 (step_imported_nat_to_rocq xL) HlowC).
        have HhighR := prop_sprop_trusted_elim _
          (step_lt_backward_strict (step_imported_nat_to_rocq xL) t HhighC).
        have HnegR := Logic.proj1 (Logic.proj2 Hparts)
          (step_imported_nat_to_rocq xL).
        have HnegR' : ~~ PR (step_imported_nat_to_rocq xL).
        { apply HnegR. apply/andP. split; assumption. }
        have Hpx := Hpred (step_imported_nat_to_rocq xL)
          xL Hround.
        exact (step_bool_neg_forward _ _ Hpx HnegR').
      * have Hpt := Hpred t (step_nat_to_imported t) (eq_refl _).
        exact (step_bool_truth_forward _ _ Hpt
          (Logic.proj2 (Logic.proj2 Hparts))).
  - intro Htarget.
    apply strictly_inhabits.
    intros HleR HnotR HtrueR.
    have Hpred1 := Hpred t1 (step_nat_to_imported t1) (eq_refl _).
    have Hpred2 := Hpred t2 (step_nat_to_imported t2) (eq_refl _).
    have Hresult := Htarget
      (step_le_forward t1 t2 HleR)
      (step_bool_neg_forward _ _ Hpred1 HnotR)
      (step_bool_truth_forward _ _ Hpred2 HtrueR).
    exact (prop_sprop_trusted_elim _
      (step_result_backward_strict PR PL t1 t2 Hpred Hresult)).

Qed.

Print Assumptions step_imported_nat_roundtrip.
Print Assumptions exists_first_intermediate_point_statement_certificate.
Print Assumptions original_exists_first_has_expected_statement.
Print Assumptions imported_exists_first_has_expected_statement.
