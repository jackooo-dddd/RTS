From mathcomp Require Import ssreflect ssrbool ssrnat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation.

(** Canonical, computation-preserving correspondence between MathComp/Rocq
    [nat] and the actual Lean [Nat] imported from the compiled
    [Prosa.Util.Subadditivity] artifact. *)
Fixpoint sub_nat_to_imported (n : nat) : Lean.Nat :=
  match n with
  | O => Lean.Nat_zero
  | S n' => Lean.Nat_succ (sub_nat_to_imported n')
  end.

Fixpoint sub_nat_to_rocq (n : Lean.Nat) : nat :=
  match n with
  | Lean.Nat_zero => O
  | Lean.Nat_succ n' => S (sub_nat_to_rocq n')
  end.

Definition SubNatRel (nR : nat) (nL : Lean.Nat) : SProp :=
  Lean.eq (sub_nat_to_imported nR) nL.

Definition SubNatFunRel (fR : nat -> nat)
    (fL : Lean.Nat -> Lean.Nat) : SProp :=
  forall nR nL, SubNatRel nR nL -> SubNatRel (fR nR) (fL nL).

Definition sub_imported_eq_sym {A : Type} (x y : A) :
    Lean.eq x y -> Lean.eq y x :=
  fun H => match H in Lean.eq _ z return Lean.eq z x with
           | Lean.eq_refl => @Lean.eq_refl A x
           end.

Definition sub_imported_eq_trans {A : Type} (x y z : A) :
    Lean.eq x y -> Lean.eq y z -> Lean.eq x z :=
  fun Hxy Hyz =>
    match Hxy in Lean.eq _ y' return Lean.eq y' z -> Lean.eq x z with
    | Lean.eq_refl => fun H => H
    end Hyz.

Definition sub_imported_eq_congr {A B : Type} (f : A -> B) (x y : A) :
    Lean.eq x y -> Lean.eq (f x) (f y) :=
  fun H => match H in Lean.eq _ z return Lean.eq (f x) (f z) with
           | Lean.eq_refl => @Lean.eq_refl B (f x)
           end.

Definition sub_imported_eq_congr2 {A B C : Type} (f : A -> B -> C)
    (x1 x2 : A) (y1 y2 : B) :
    Lean.eq x1 x2 -> Lean.eq y1 y2 -> Lean.eq (f x1 y1) (f x2 y2) :=
  fun Hx Hy =>
    match Hx in Lean.eq _ x' return Lean.eq (f x1 y1) (f x' y2) with
    | Lean.eq_refl => sub_imported_eq_congr (f x1) y1 y2 Hy
    end.

Lemma sub_nat_rocq_roundtrip (n : nat) :
  Logic.eq (sub_nat_to_rocq (sub_nat_to_imported n)) n.
Proof. induction n; cbn; first reflexivity. f_equal. exact IHn. Qed.

Lemma sub_nat_imported_roundtrip (n : Lean.Nat) :
  Lean.eq (sub_nat_to_imported (sub_nat_to_rocq n)) n.
Proof.
  induction n; cbn.
  - exact (@Lean.eq_refl Lean.Nat Lean.Nat_zero).
  - exact (sub_imported_eq_congr Lean.Nat_succ _ _ IHn).
Qed.

Definition sub_nat_rel_canonical (n : nat) :
    SubNatRel n (sub_nat_to_imported n) :=
  @Lean.eq_refl Lean.Nat (sub_nat_to_imported n).

Definition sub_nat_rel_surjective (n : Lean.Nat) :
    SubNatRel (sub_nat_to_rocq n) n := sub_nat_imported_roundtrip n.

(** These aliases are definitionally the actual typeclass-resolved operations
    occurring in the imported target declarations. *)
Definition sub_imported_add (a b : Lean.Nat) : Lean.Nat :=
  ImportedSubadditivity.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedSubadditivity.instHAdd_inst1 Lean.Nat
      ImportedSubadditivity.instAddNat) a b.

Definition sub_imported_mul (a b : Lean.Nat) : Lean.Nat :=
  ImportedSubadditivity.HMul_hMul_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedSubadditivity.instHMul_inst1 Lean.Nat
      ImportedSubadditivity.instMulNat) a b.

Definition sub_imported_le (a b : Lean.Nat) : SProp :=
  ImportedSubadditivity.LE_le_inst1 Lean.Nat
    ImportedSubadditivity.instLENat a b.

Definition sub_imported_lt (a b : Lean.Nat) : SProp :=
  ImportedSubadditivity.LT_lt_inst1 Lean.Nat
    ImportedSubadditivity.instLTNat a b.

Definition sub_imported_zero : Lean.Nat :=
  ImportedSubadditivity.OfNat_ofNat_inst1 Lean.Nat Lean.Nat_zero
    (ImportedSubadditivity.instOfNatNat Lean.Nat_zero).

Lemma sub_imported_add_is_core (a b : Lean.Nat) :
  Lean.eq (sub_imported_add a b) (Lean.Nat_add a b).
Proof. exact (@Lean.eq_refl Lean.Nat (Lean.Nat_add a b)). Qed.

Lemma sub_imported_mul_is_core (a b : Lean.Nat) :
  Lean.eq (sub_imported_mul a b) (Lean.Nat_mul a b).
Proof. exact (@Lean.eq_refl Lean.Nat (Lean.Nat_mul a b)). Qed.

Lemma sub_imported_le_is_core (a b : Lean.Nat) :
  forall H : sub_imported_le a b, Lean.Nat_le a b.
Proof. exact (fun H => H). Qed.

Lemma sub_imported_lt_is_core (a b : Lean.Nat) :
  forall H : sub_imported_lt a b, ImportedSubadditivity.Nat_lt a b.
Proof. exact (fun H => H). Qed.

Lemma sub_imported_zero_is_core :
  Lean.eq sub_imported_zero Lean.Nat_zero.
Proof. exact (@Lean.eq_refl Lean.Nat Lean.Nat_zero). Qed.

Lemma sub_add_canonical (a b : nat) :
  Lean.eq
    (sub_imported_add (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (a + b)).
Proof.
  induction b as [|b IH].
  - rewrite addn0. exact (@Lean.eq_refl Lean.Nat (sub_nat_to_imported a)).
  - rewrite addnS. cbn [sub_nat_to_imported sub_imported_add].
    exact (sub_imported_eq_congr Lean.Nat_succ _ _ IH).
Qed.

Lemma sub_mul_canonical (a b : nat) :
  Lean.eq
    (sub_imported_mul (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (a * b)).
Proof.
  induction b as [|b IH].
  - rewrite muln0. exact (@Lean.eq_refl Lean.Nat Lean.Nat_zero).
  - rewrite mulnS addnC. cbn [sub_nat_to_imported sub_imported_mul].
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_congr (fun z => Lean.Nat_add z
          (sub_nat_to_imported a)) _ _ IH)
      (sub_add_canonical (a * b) a)).
Qed.

Lemma sub_add_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR + bR) (sub_imported_add aL bL).
Proof.
  intros Ha Hb. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (sub_add_canonical aR bR))
    (sub_imported_eq_congr2 sub_imported_add _ _ _ _ Ha Hb)).
Qed.

Lemma sub_mul_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR * bR) (sub_imported_mul aL bL).
Proof.
  intros Ha Hb. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (sub_mul_canonical aR bR))
    (sub_imported_eq_congr2 sub_imported_mul _ _ _ _ Ha Hb)).
Qed.

Inductive SubNatTrue : SProp := sub_nat_truth_intro.
Inductive SubNatFalse : SProp := .

Definition SubNatTruth (b : bool) : SProp :=
  match b with true => SubNatTrue | false => SubNatFalse end.

Definition sub_nat_false_elim (P : SProp) (H : SubNatTruth false) : P :=
  match H return P with end.

Definition sub_nat_prop_to_truth (b : bool) : is_true b -> SubNatTruth b :=
  match b return is_true b -> SubNatTruth b with
  | true => fun _ => sub_nat_truth_intro
  | false => fun H =>
      match H in Logic.eq _ z return
        match z with true => SubNatTruth false | false => SubNatTruth true end
      with Logic.eq_refl => sub_nat_truth_intro end
  end.

Definition sub_nat_truth_to_strict_prop (b : bool) :
    SubNatTruth b -> StrictlyInhabited (is_true b) :=
  match b return SubNatTruth b -> StrictlyInhabited (is_true b) with
  | true => fun _ => strictly_inhabits (Logic.eq_refl true)
  | false => fun H => sub_nat_false_elim _ H
  end.

Fixpoint sub_imported_zero_le (m : Lean.Nat) :
    Lean.Nat_le Lean.Nat_zero m :=
  match m with
  | Lean.Nat_zero => Lean.Nat_le_refl Lean.Nat_zero
  | Lean.Nat_succ m' =>
      Lean.Nat_le_step Lean.Nat_zero m' (sub_imported_zero_le m')
  end.

Fixpoint sub_imported_le_succ_succ (n m : Lean.Nat)
    (H : Lean.Nat_le n m) : Lean.Nat_le (Lean.Nat_succ n) (Lean.Nat_succ m) :=
  match H with
  | Lean.Nat_le_refl => Lean.Nat_le_refl (Lean.Nat_succ n)
  | Lean.Nat_le_step k H' =>
      Lean.Nat_le_step (Lean.Nat_succ n) (Lean.Nat_succ k)
        (sub_imported_le_succ_succ n k H')
  end.

Fixpoint sub_imported_le_left_pred (n m : Lean.Nat)
    (H : Lean.Nat_le (Lean.Nat_succ n) m) : Lean.Nat_le n m :=
  match H with
  | Lean.Nat_le_refl =>
      Lean.Nat_le_step n n (Lean.Nat_le_refl n)
  | Lean.Nat_le_step k H' =>
      Lean.Nat_le_step n k (sub_imported_le_left_pred n k H')
  end.

Definition sub_imported_le_succ_inv (n m : Lean.Nat)
    (H : Lean.Nat_le (Lean.Nat_succ n) (Lean.Nat_succ m)) :
    Lean.Nat_le n m :=
  match H in Lean.Nat_le _ z return
    match z with
    | Lean.Nat_zero => SubNatTruth true
    | Lean.Nat_succ k => Lean.Nat_le n k
    end
  with
  | Lean.Nat_le_refl => Lean.Nat_le_refl n
  | Lean.Nat_le_step k H' => sub_imported_le_left_pred n k H'
  end.

Definition sub_imported_succ_not_le_zero (n : Lean.Nat)
    (H : Lean.Nat_le (Lean.Nat_succ n) Lean.Nat_zero) : SubNatTruth false :=
  match H in Lean.Nat_le _ z return
    match z with
    | Lean.Nat_zero => SubNatTruth false
    | Lean.Nat_succ _ => SubNatTruth true
    end
  with
  | Lean.Nat_le_refl => sub_nat_truth_intro
  | Lean.Nat_le_step _ _ => sub_nat_truth_intro
  end.

Fixpoint sub_rocq_le_to_imported (n m : nat) :
    SubNatTruth (leq n m) ->
    Lean.Nat_le (sub_nat_to_imported n) (sub_nat_to_imported m) :=
  match n, m return SubNatTruth (leq n m) ->
      Lean.Nat_le (sub_nat_to_imported n) (sub_nat_to_imported m)
  with
  | O, m' => fun _ => sub_imported_zero_le (sub_nat_to_imported m')
  | S n', O => sub_nat_false_elim _
  | S n', S m' => fun H =>
      sub_imported_le_succ_succ _ _ (sub_rocq_le_to_imported n' m' H)
  end.

Fixpoint sub_imported_le_to_rocq (n m : nat) :
    Lean.Nat_le (sub_nat_to_imported n) (sub_nat_to_imported m) ->
    SubNatTruth (leq n m) :=
  match n, m return
      Lean.Nat_le (sub_nat_to_imported n) (sub_nat_to_imported m) ->
      SubNatTruth (leq n m)
  with
  | O, _ => fun _ => sub_nat_truth_intro
  | S n', O => sub_imported_succ_not_le_zero (sub_nat_to_imported n')
  | S n', S m' => fun H => sub_imported_le_to_rocq n' m'
      (sub_imported_le_succ_inv _ _ H)
  end.

Definition sub_imported_le_transport (a a' b b' : Lean.Nat) :
    Lean.eq a a' -> Lean.eq b b' -> Lean.Nat_le a b -> Lean.Nat_le a' b' :=
  fun Ha Hb H =>
    match Ha in Lean.eq _ x return
      Lean.eq b b' -> Lean.Nat_le a b -> Lean.Nat_le x b'
    with
    | Lean.eq_refl => fun Hb' H' =>
        match Hb' in Lean.eq _ y return Lean.Nat_le a b -> Lean.Nat_le a y with
        | Lean.eq_refl => fun H'' => H''
        end H'
    end Hb H.

Lemma sub_nat_le_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (leq aR bR)) (sub_imported_le aL bL).
Proof.
  intros Ha Hb. apply prop_sprop_rel_intro.
  - intro Hle. unfold sub_imported_le.
    exact (sub_imported_le_transport _ _ _ _ Ha Hb
      (sub_rocq_le_to_imported aR bR (sub_nat_prop_to_truth _ Hle))).
  - intro Hle. apply sub_nat_truth_to_strict_prop.
    apply sub_imported_le_to_rocq.
    exact (sub_imported_le_transport _ _ _ _
      (sub_imported_eq_sym _ _ Ha) (sub_imported_eq_sym _ _ Hb) Hle).
Qed.

Lemma sub_nat_lt_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (ltn aR bR)) (sub_imported_lt aL bL).
Proof.
  intros Ha Hb.
  change (PropSPropRel (is_true (leq (S aR) bR))
    (Lean.Nat_le (Lean.Nat_succ aL) bL)).
  apply sub_nat_le_correspondence.
  - exact (sub_imported_eq_congr Lean.Nat_succ _ _ Ha).
  - exact Hb.
Qed.

Lemma sub_nat_eq_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof.
  intros Ha Hb. apply prop_sprop_rel_intro.
  - intro Heq. destruct Heq.
    exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_sym _ _ Ha) Hb).
  - intro Heq.
    apply strictly_inhabits.
    have Hcanonical : Lean.eq (sub_nat_to_imported aR)
        (sub_nat_to_imported bR) :=
      sub_imported_eq_trans _ _ _ Ha
        (sub_imported_eq_trans _ _ _ Heq (sub_imported_eq_sym _ _ Hb)).
    have Hdecoded := f_equal sub_nat_to_rocq
      (imported_eq_to_coq_eq _ _ Hcanonical).
    rewrite (sub_nat_rocq_roundtrip aR) in Hdecoded.
    rewrite (sub_nat_rocq_roundtrip bR) in Hdecoded.
    exact Hdecoded.
Qed.

Print Assumptions sub_nat_imported_roundtrip.
Print Assumptions sub_add_correspondence.
Print Assumptions sub_mul_correspondence.
Print Assumptions sub_nat_le_correspondence.
Print Assumptions sub_nat_lt_correspondence.
Print Assumptions sub_nat_eq_correspondence.
