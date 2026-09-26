(* Re-bound copy of accepted certificates/analysis_facts_model_sbf_periodic/NatSubCorrespondence.v for the
   analysis/facts/sporadic/arrival_bound artifact; only the imported module name differs. *)
(* Re-bound copy of the accepted analysis/definitions/sbf/periodic replay of NatSubCorrespondence.v for the
   analysis/facts/model/sbf/periodic artifact; only the imported module name differs. *)
(** Mechanical replay of accepted bridge source 7d8700c52d59ff709996d96f2e9d3bd88e76d4c3914808fbeaf4866a68f22d57; imported identity ImportedNat -> ImportedFactsSporadicArrivalBound. DivMod drops the unused ImportedNat import. *)
From mathcomp Require Import ssreflect ssrbool ssrnat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsSporadicArrivalBound.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.

(** Adapter for the operations that occur in the actual freshly imported
    [Prosa.Util.Nat] theorem types. *)
Definition nat_target_add (a b : Lean.Nat) : Lean.Nat :=
  ImportedFactsSporadicArrivalBound.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedFactsSporadicArrivalBound.instHAdd_inst1 Lean.Nat ImportedFactsSporadicArrivalBound.instAddNat) a b.

Definition nat_target_sub (a b : Lean.Nat) : Lean.Nat :=
  ImportedFactsSporadicArrivalBound.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedFactsSporadicArrivalBound.instHSub_inst1 Lean.Nat ImportedFactsSporadicArrivalBound.instSubNat) a b.

Definition nat_target_le (a b : Lean.Nat) : SProp :=
  ImportedFactsSporadicArrivalBound.LE_le_inst1 Lean.Nat ImportedFactsSporadicArrivalBound.instLENat a b.

Lemma nat_target_add_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR + bR) (nat_target_add aL bL).
Proof.
  intros Ha Hb. exact (sub_add_correspondence aR aL bR bL Ha Hb).
Qed.

Lemma nat_target_le_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (leq aR bR)) (nat_target_le aL bL).
Proof.
  intros Ha Hb. exact (sub_nat_le_correspondence aR aL bR bL Ha Hb).
Qed.

(** The actual compiled Lean subtraction is a course-of-values recursion on
    the amount being subtracted.  Its two computation equations are
    definitionally true in the imported artifact. *)
Lemma nat_target_sub_zero (a : Lean.Nat) :
  Lean.eq (nat_target_sub a Lean.Nat_zero) a.
Proof. exact (@Lean.eq_refl Lean.Nat a). Qed.

Lemma nat_target_sub_succ (a b : Lean.Nat) :
  Lean.eq (nat_target_sub a (Lean.Nat_succ b))
    (ImportedFactsSporadicArrivalBound.Nat_pred (nat_target_sub a b)).
Proof.
  exact (@Lean.eq_refl Lean.Nat
    (ImportedFactsSporadicArrivalBound.Nat_pred (nat_target_sub a b))).
Qed.

Fixpoint rocq_iterated_pred (a b : nat) : nat :=
  match b with
  | O => a
  | S b' => Nat.pred (rocq_iterated_pred a b')
  end.

Lemma rocq_iterated_pred_is_subn (a b : nat) :
  Logic.eq (rocq_iterated_pred a b) (a - b).
Proof.
  revert a. induction b as [|b IH]; intro a; cbn [rocq_iterated_pred].
  - rewrite subn0. reflexivity.
  - rewrite (IH a). exact (Logic.eq_sym (subnS a b)).
Qed.

Definition nat_target_pred_canonical (n : nat) :
  Lean.eq (ImportedFactsSporadicArrivalBound.Nat_pred (sub_nat_to_imported n))
    (sub_nat_to_imported (Nat.pred n)) :=
  match n return
    Lean.eq (ImportedFactsSporadicArrivalBound.Nat_pred (sub_nat_to_imported n))
      (sub_nat_to_imported (Nat.pred n))
  with
  | O => @Lean.eq_refl Lean.Nat Lean.Nat_zero
  | S n' => @Lean.eq_refl Lean.Nat (sub_nat_to_imported n')
  end.

Lemma nat_target_sub_iterated_pred (a b : nat) :
  Lean.eq
    (nat_target_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (rocq_iterated_pred a b)).
Proof.
  induction b as [|b IH].
  - exact (nat_target_sub_zero (sub_nat_to_imported a)).
  - exact (sub_imported_eq_trans _ _ _
      (nat_target_sub_succ _ _)
      (sub_imported_eq_trans _ _ _
        (sub_imported_eq_congr ImportedFactsSporadicArrivalBound.Nat_pred _ _ IH)
        (nat_target_pred_canonical (rocq_iterated_pred a b)))).
Qed.

(** Direct computation proof for truncated subtraction.  This covers both
    branches: a positive residual and truncation to zero. *)
Lemma nat_target_sub_canonical (a b : nat) :
  Lean.eq
    (nat_target_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (a - b)).
Proof.
  exact (sub_imported_eq_trans _ _ _
    (nat_target_sub_iterated_pred a b)
    (coq_eq_to_imported_eq _ _
      (f_equal sub_nat_to_imported (rocq_iterated_pred_is_subn a b)))).
Qed.

Lemma nat_target_sub_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR - bR) (nat_target_sub aL bL).
Proof.
  intros Ha Hb. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (nat_target_sub_canonical aR bR))
    (sub_imported_eq_congr2 nat_target_sub _ _ _ _ Ha Hb)).
Qed.

(** Explicit branch witnesses requested by the translation policy. *)
Lemma nat_target_sub_nontruncated a b :
  is_true (leq b a) ->
  SubNatRel (a - b)
    (nat_target_sub (sub_nat_to_imported a) (sub_nat_to_imported b)).
Proof. intros _. apply nat_target_sub_correspondence; apply sub_nat_rel_canonical. Qed.

Lemma rocq_sub_truncates a b :
  is_true (ltn a b) -> Logic.eq (a - b) O.
Proof.
  move: a. elim: b => [|b IH] [|a] //= H. exact: IH.
Qed.

Lemma nat_target_sub_truncated a b :
  is_true (ltn a b) ->
  SubNatRel O
    (nat_target_sub (sub_nat_to_imported a) (sub_nat_to_imported b)).
Proof.
  intro Hlt. have Hz : Logic.eq (a - b) O := rocq_sub_truncates a b Hlt.
  rewrite <- Hz. apply nat_target_sub_correspondence; apply sub_nat_rel_canonical.
Qed.

Print Assumptions nat_target_sub_canonical.
Print Assumptions nat_target_sub_correspondence.
Print Assumptions nat_target_sub_nontruncated.
Print Assumptions nat_target_sub_truncated.
