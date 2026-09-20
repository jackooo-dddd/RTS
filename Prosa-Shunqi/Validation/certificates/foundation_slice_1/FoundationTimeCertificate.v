From Stdlib Require Import Arith.PeanoNat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTime.
From prosa Require Import behavior.time.

(** The imported Lean [Nat] is a distinct inductive in Rocq.  These maps are
    the minimal representation bridge required for the two time aliases. *)
Fixpoint rocq_nat_to_imported (n : nat) : Nat :=
  match n with
  | O => Nat_zero
  | S n' => Nat_succ (rocq_nat_to_imported n')
  end.

Fixpoint imported_nat_to_rocq (n : Nat) : nat :=
  match n with
  | Nat_zero => O
  | Nat_succ n' => S (imported_nat_to_rocq n')
  end.

Definition imported_nat_succ_congr (a b : Nat) :
    eq a b -> eq (Nat_succ a) (Nat_succ b) :=
  fun H =>
    match H in eq _ z return eq (Nat_succ a) (Nat_succ z) with
    | eq_refl _ => eq_refl (Nat_succ a)
    end.

Lemma rocq_nat_roundtrip (n : nat) :
  Logic.eq (imported_nat_to_rocq (rocq_nat_to_imported n)) n.
Proof.
  induction n; cbn.
  - reflexivity.
  - f_equal. exact IHn.
Qed.

Lemma imported_nat_roundtrip (n : Nat) :
  eq (rocq_nat_to_imported (imported_nat_to_rocq n)) n.
Proof.
  induction n; cbn.
  - exact (eq_refl Nat_zero).
  - exact (imported_nat_succ_congr _ _ IHn).
Qed.

Definition DurationRel
    (dR : prosa.behavior.time.duration)
    (dL : Prosa_Behavior_Time_duration) : SProp :=
  eq (rocq_nat_to_imported dR) dL.

Definition InstantRel
    (tR : prosa.behavior.time.instant)
    (tL : Prosa_Behavior_Time_instant) : SProp :=
  eq (rocq_nat_to_imported tR) tL.

Definition duration_to_imported
    (d : prosa.behavior.time.duration) : Prosa_Behavior_Time_duration :=
  rocq_nat_to_imported d.

Definition imported_to_duration
    (d : Prosa_Behavior_Time_duration) : prosa.behavior.time.duration :=
  imported_nat_to_rocq d.

Lemma duration_relation_total_from_rocq d :
  DurationRel d (duration_to_imported d).
Proof. exact (eq_refl _). Qed.

Lemma duration_rocq_roundtrip_certificate d :
  Logic.eq (imported_to_duration (duration_to_imported d)) d.
Proof. exact (rocq_nat_roundtrip d). Qed.

Lemma duration_imported_roundtrip_certificate d :
  eq (duration_to_imported (imported_to_duration d)) d.
Proof. exact (imported_nat_roundtrip d). Qed.

Definition instant_to_imported
    (t : prosa.behavior.time.instant) : Prosa_Behavior_Time_instant :=
  rocq_nat_to_imported t.

Definition imported_to_instant
    (t : Prosa_Behavior_Time_instant) : prosa.behavior.time.instant :=
  imported_nat_to_rocq t.

Lemma instant_relation_total_from_rocq t :
  InstantRel t (instant_to_imported t).
Proof. exact (eq_refl _). Qed.

Lemma instant_rocq_roundtrip_certificate t :
  Logic.eq (imported_to_instant (instant_to_imported t)) t.
Proof. exact (rocq_nat_roundtrip t). Qed.

Lemma instant_imported_roundtrip_certificate t :
  eq (instant_to_imported (imported_to_instant t)) t.
Proof. exact (imported_nat_roundtrip t). Qed.

