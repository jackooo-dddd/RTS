From mathcomp Require Import ssreflect ssrbool ssrnat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSearchArg ImportedSubadditivity.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.
Require Import GeneratedSearchArgSource.

Fixpoint sa_bool_to_imported (b : bool) : ImportedSearchArg.Bool :=
  match b with
  | true => ImportedSearchArg.Bool_true
  | false => ImportedSearchArg.Bool_false
  end.

Definition sa_option_to_imported (o : option nat) :
    ImportedSearchArg.Option_inst1 Lean.Nat :=
  match o with
  | None => ImportedSearchArg.Option_none_inst1 Lean.Nat
  | Some n => ImportedSearchArg.Option_some_inst1 Lean.Nat
      (sub_nat_to_imported n)
  end.

Definition sa_target_f {T : Type} (f : nat -> T) : Lean.Nat -> T :=
  fun n => f (sub_nat_to_rocq n).

Definition sa_target_P {T : Type} (P : T -> bool) :
    T -> ImportedSearchArg.Bool :=
  fun x => sa_bool_to_imported (P x).

Definition sa_target_R {T : Type} (R : T -> T -> bool) :
    T -> T -> ImportedSearchArg.Bool :=
  fun x y => sa_bool_to_imported (R x y).

Definition sa_target_search {T : Type}
    (f : nat -> T) (P : T -> bool) (R : T -> T -> bool)
    (a b : nat) : ImportedSearchArg.Option_inst1 Lean.Nat :=
  ImportedSearchArg.Prosa_Util_SearchArg_search_arg T
    (sa_target_f f) (sa_target_P P) (sa_target_R R)
    (sub_nat_to_imported a) (sub_nat_to_imported b).

Definition sa_imported_false_elim (Q : SProp)
    (H : ImportedSearchArg.False) : Q := match H return Q with end.

Definition sa_imported_false_to_strict (H : ImportedSearchArg.False) :
    StrictlyInhabited Logic.False := match H with end.

Lemma sa_ite_true {A : Type} (t e : A) :
  Lean.eq
    (ImportedSearchArg.ite A
      (Lean.eq ImportedSearchArg.Bool_true ImportedSearchArg.Bool_true)
      (ImportedSearchArg.instDecidableEqBool
        ImportedSearchArg.Bool_true ImportedSearchArg.Bool_true) t e) t.
Proof.
  unfold ImportedSearchArg.ite.
  destruct (ImportedSearchArg.instDecidableEqBool
    ImportedSearchArg.Bool_true ImportedSearchArg.Bool_true) as [Hfalse|Htrue].
  - exact (sa_imported_false_elim _
      (Hfalse (@Lean.eq_refl ImportedSearchArg.Bool
        ImportedSearchArg.Bool_true))).
  - exact (@Lean.eq_refl A t).
Qed.

Lemma sa_ite_false {A : Type} (t e : A) :
  Lean.eq
    (ImportedSearchArg.ite A
      (Lean.eq ImportedSearchArg.Bool_false ImportedSearchArg.Bool_true)
      (ImportedSearchArg.instDecidableEqBool
        ImportedSearchArg.Bool_false ImportedSearchArg.Bool_true) t e) e.
Proof.
  unfold ImportedSearchArg.ite.
  destruct (ImportedSearchArg.instDecidableEqBool
    ImportedSearchArg.Bool_false ImportedSearchArg.Bool_true) as [Hfalse|Htrue].
  - exact (@Lean.eq_refl A e).
  - exact (sa_imported_false_elim _
      (ImportedSearchArg.Bool_noConfusion_inst1 ImportedSearchArg.False
        ImportedSearchArg.Bool_false ImportedSearchArg.Bool_true Htrue)).
Qed.

Lemma sa_base {T : Type} (f : nat -> T) (P : T -> bool)
    (R : T -> T -> bool) (a : nat) :
  Lean.eq (sa_target_search f P R a 0)
    (sa_option_to_imported
      (GeneratedSearchArgSource.search_arg f P R a 0)).
Proof.
  unfold sa_target_search.
  have H := ImportedSearchArg.Prosa_Util_SearchArg_search_arg_eq_1
    T (sa_target_f f) (sa_target_P P) (sa_target_R R)
    (sub_nat_to_imported a).
  exact (sub_imported_eq_trans _ _ _ H
    (@Lean.eq_refl (ImportedSearchArg.Option_inst1 Lean.Nat)
      (ImportedSearchArg.Option_none_inst1 Lean.Nat))).
Qed.

Definition sa_source_step {T : Type} (f : nat -> T) (P : T -> bool)
    (R : T -> T -> bool) (b : nat) (o : option nat) : option nat :=
  match o with
  | None => if P (f b) then Some b else None
  | Some x => if P (f b) && R (f b) (f x) then Some b else Some x
  end.

Definition sa_target_step {T : Type} (f : nat -> T) (P : T -> bool)
    (R : T -> T -> bool) (b : nat)
    (o : ImportedSearchArg.Option_inst1 Lean.Nat) :
    ImportedSearchArg.Option_inst1 Lean.Nat :=
  ImportedSearchArg.Prosa_Util_SearchArg_search_arg_match_1
    (fun _ => ImportedSearchArg.Option_inst1 Lean.Nat) o
    (fun _ =>
      ImportedSearchArg.ite (ImportedSearchArg.Option_inst1 Lean.Nat)
        (Lean.eq
          (sa_target_P P (sa_target_f f (sub_nat_to_imported b)))
          ImportedSearchArg.Bool_true)
        (ImportedSearchArg.instDecidableEqBool
          (sa_target_P P (sa_target_f f (sub_nat_to_imported b)))
          ImportedSearchArg.Bool_true)
        (ImportedSearchArg.Option_some_inst1 Lean.Nat
          (sub_nat_to_imported b))
        (ImportedSearchArg.Option_none_inst1 Lean.Nat))
    (fun x =>
      ImportedSearchArg.ite (ImportedSearchArg.Option_inst1 Lean.Nat)
        (Lean.eq
          (ImportedSearchArg.Bool_and
            (sa_target_P P (sa_target_f f (sub_nat_to_imported b)))
            (sa_target_R R (sa_target_f f (sub_nat_to_imported b))
              (sa_target_f f x)))
          ImportedSearchArg.Bool_true)
        (ImportedSearchArg.instDecidableEqBool
          (ImportedSearchArg.Bool_and
            (sa_target_P P (sa_target_f f (sub_nat_to_imported b)))
            (sa_target_R R (sa_target_f f (sub_nat_to_imported b))
              (sa_target_f f x)))
          ImportedSearchArg.Bool_true)
        (ImportedSearchArg.Option_some_inst1 Lean.Nat
          (sub_nat_to_imported b))
        (ImportedSearchArg.Option_some_inst1 Lean.Nat x)).

Lemma sa_step_canonical {T : Type} (f : nat -> T) (P : T -> bool)
    (R : T -> T -> bool) (b : nat)
    (oR : option nat) (oL : ImportedSearchArg.Option_inst1 Lean.Nat) :
  Lean.eq oL (sa_option_to_imported oR) ->
  Lean.eq (sa_target_step f P R b oL)
    (sa_option_to_imported (sa_source_step f P R b oR)).
Proof.
  intro Ho.
  refine (sub_imported_eq_trans _ _ _
    (sub_imported_eq_congr (sa_target_step f P R b) _ _ Ho) _).
  destruct oR as [x|].
  - unfold sa_target_step, sa_source_step, sa_option_to_imported,
      sa_target_P, sa_target_R, sa_target_f.
    unfold ImportedSearchArg.Prosa_Util_SearchArg_search_arg_match_1,
      ImportedSearchArg.Option_casesOn_inst2.
    cbn.
    rw !sub_nat_rocq_roundtrip.
    destruct (P (f b)), (R (f b) (f x));
      cbn [sa_bool_to_imported ImportedSearchArg.Bool_and
        ImportedSearchArg.Bool_and_match_1].
    + unfold ImportedSearchArg.Bool_and,
        ImportedSearchArg.Bool_and_match_1; cbn.
      exact (sa_ite_true
        (ImportedSearchArg.Option_some_inst1 Lean.Nat (sub_nat_to_imported b))
        (ImportedSearchArg.Option_some_inst1 Lean.Nat (sub_nat_to_imported x))).
    + unfold ImportedSearchArg.Bool_and,
        ImportedSearchArg.Bool_and_match_1; cbn.
      exact (sa_ite_false
        (ImportedSearchArg.Option_some_inst1 Lean.Nat (sub_nat_to_imported b))
        (ImportedSearchArg.Option_some_inst1 Lean.Nat (sub_nat_to_imported x))).
    + unfold ImportedSearchArg.Bool_and,
        ImportedSearchArg.Bool_and_match_1; cbn.
      exact (sa_ite_false
        (ImportedSearchArg.Option_some_inst1 Lean.Nat (sub_nat_to_imported b))
        (ImportedSearchArg.Option_some_inst1 Lean.Nat (sub_nat_to_imported x))).
    + unfold ImportedSearchArg.Bool_and,
        ImportedSearchArg.Bool_and_match_1; cbn.
      exact (sa_ite_false
        (ImportedSearchArg.Option_some_inst1 Lean.Nat (sub_nat_to_imported b))
        (ImportedSearchArg.Option_some_inst1 Lean.Nat (sub_nat_to_imported x))).
  - unfold sa_target_step, sa_source_step, sa_option_to_imported,
      sa_target_P, sa_target_f.
    unfold ImportedSearchArg.Prosa_Util_SearchArg_search_arg_match_1,
      ImportedSearchArg.Option_casesOn_inst2.
    cbn.
    rw sub_nat_rocq_roundtrip.
    destruct (P (f b)); cbn [sa_bool_to_imported].
    + exact (sa_ite_true
        (ImportedSearchArg.Option_some_inst1 Lean.Nat (sub_nat_to_imported b))
        (ImportedSearchArg.Option_none_inst1 Lean.Nat)).
    + exact (sa_ite_false
        (ImportedSearchArg.Option_some_inst1 Lean.Nat (sub_nat_to_imported b))
        (ImportedSearchArg.Option_none_inst1 Lean.Nat)).
Qed.

Definition sa_target_lt (a b : nat) : SProp :=
  ImportedSearchArg.LT_lt_inst1 Lean.Nat ImportedSearchArg.instLTNat
    (sub_nat_to_imported a) (sub_nat_to_imported b).

Lemma sa_lt_ite_canonical {A : Type} (a b : nat) (t e : A) :
  Lean.eq
    (ImportedSearchArg.ite A (sa_target_lt a b)
      (ImportedSearchArg.Nat_decLt
        (sub_nat_to_imported a) (sub_nat_to_imported b)) t e)
    (if ltn a b then t else e).
Proof.
  unfold ImportedSearchArg.ite.
  have Hcorr := sub_nat_lt_correspondence a (sub_nat_to_imported a)
    b (sub_nat_to_imported b) (sub_nat_rel_canonical a)
      (sub_nat_rel_canonical b).
  destruct (ImportedSearchArg.Nat_decLt
    (sub_nat_to_imported a) (sub_nat_to_imported b)) as [Hfalse|Htrue].
  - have Hnot : ~ is_true (ltn a b).
    { intro HR.
      have HF : ImportedSearchArg.False :=
        Hfalse (prop_to_sprop _ _ Hcorr HR).
      exact (interpret_strict Logic.False (sa_imported_false_to_strict HF)). }
    have Hab : ltn a b = false.
    { destruct (ltn a b) eqn:E; first exfalso.
      - apply Hnot. exact (Logic.eq_refl true).
      - reflexivity. }
    rw Hab. exact (@Lean.eq_refl A e).
  - have Hab : is_true (ltn a b) := sprop_to_prop _ _ Hcorr Htrue.
    rw Hab. exact (@Lean.eq_refl A t).
Qed.

Lemma sa_source_eq_2 {T : Type} (f : nat -> T) (P : T -> bool)
    (R : T -> T -> bool) (a b : nat) :
  Logic.eq
    (GeneratedSearchArgSource.search_arg f P R a (S b))
    (if ltn a (S b)
     then sa_source_step f P R b
       (GeneratedSearchArgSource.search_arg f P R a b)
     else None).
Proof. reflexivity. Qed.

Lemma sa_conditional_step_canonical {T : Type}
    (f : nat -> T) (P : T -> bool) (R : T -> T -> bool)
    (a b : nat) (oR : option nat)
    (oL : ImportedSearchArg.Option_inst1 Lean.Nat) :
  Lean.eq oL (sa_option_to_imported oR) ->
  Lean.eq
    (if ltn a (S b)
     then sa_target_step f P R b oL
     else ImportedSearchArg.Option_none_inst1 Lean.Nat)
    (sa_option_to_imported
      (if ltn a (S b)
       then sa_source_step f P R b oR
       else None)).
Proof.
  intro Ho. destruct (ltn a (S b)).
  - apply sa_step_canonical. exact Ho.
  - exact (@Lean.eq_refl (ImportedSearchArg.Option_inst1 Lean.Nat)
      (ImportedSearchArg.Option_none_inst1 Lean.Nat)).
Qed.

Theorem search_arg_definition_certificate {T : Type}
    (f : nat -> T) (P : T -> bool) (R : T -> T -> bool) :
  forall a b : nat,
    Lean.eq (sa_target_search f P R a b)
      (sa_option_to_imported
        (GeneratedSearchArgSource.search_arg f P R a b)).
Proof.
  intros a b. revert a. induction b as [|b IH]; intro a.
  - exact (sa_base f P R a).
  - unfold sa_target_search.
    have Heq :=
      ImportedSearchArg.Prosa_Util_SearchArg_search_arg_eq_2 T
        (sa_target_f f) (sa_target_P P) (sa_target_R R)
        (sub_nat_to_imported a) (sub_nat_to_imported b).
    refine (sub_imported_eq_trans _ _ _ Heq _).
    have Houter := sa_lt_ite_canonical
      (A := ImportedSearchArg.Option_inst1 Lean.Nat) a (S b)
      (sa_target_step f P R b
        (ImportedSearchArg.Prosa_Util_SearchArg_search_arg T
          (sa_target_f f) (sa_target_P P) (sa_target_R R)
          (sub_nat_to_imported a) (sub_nat_to_imported b)))
      (ImportedSearchArg.Option_none_inst1 Lean.Nat).
    refine (sub_imported_eq_trans _ _ _ Houter _).
    have Hmiddle := sa_conditional_step_canonical f P R a b
      (GeneratedSearchArgSource.search_arg f P R a b)
      (ImportedSearchArg.Prosa_Util_SearchArg_search_arg T
        (sa_target_f f) (sa_target_P P) (sa_target_R R)
        (sub_nat_to_imported a) (sub_nat_to_imported b)) (IH a).
    refine (sub_imported_eq_trans _ _ _ Hmiddle _).
    have Hsrc := sa_source_eq_2 f P R a b.
    exact (sub_imported_eq_sym _ _
      (coq_eq_to_imported_eq _ _ (f_equal sa_option_to_imported Hsrc))).
Qed.

Print Assumptions sa_base.
Print Assumptions sa_step_canonical.
Print Assumptions sa_lt_ite_canonical.
Print Assumptions search_arg_definition_certificate.
