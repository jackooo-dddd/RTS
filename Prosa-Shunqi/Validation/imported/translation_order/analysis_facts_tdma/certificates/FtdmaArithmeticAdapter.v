(* Re-bound copy of the accepted certificates/model_schedule_tdma/TdmaArithmeticAdapter.v:
   only the imported module (ImportedTdmaProjectedFull -> ImportedFactsTdma)
   and certificate module names (TdmaX -> FtdmaX) are renamed. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsTdma.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  FtdmaBaseAdapter.

(** The arithmetic operations are the exact constants used by the imported
    TDMA time-slot body.  The three Euclidean facts below have exported Lean
    proof bodies, not declaration-only assumptions. *)
Definition tdma_nat_add (a b : Lean.Nat) : Lean.Nat :=
  ImportedFactsTdma.HAdd_hAdd_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedFactsTdma.instHAdd_inst1 Lean.Nat
      ImportedFactsTdma.instAddNat) a b.

Definition tdma_nat_mul (a b : Lean.Nat) : Lean.Nat :=
  ImportedFactsTdma.HMul_hMul_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedFactsTdma.instHMul_inst1 Lean.Nat
      ImportedFactsTdma.instMulNat) a b.

Definition tdma_nat_sub (a b : Lean.Nat) : Lean.Nat :=
  ImportedFactsTdma.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedFactsTdma.instHSub_inst1 Lean.Nat
      ImportedFactsTdma.instSubNat) a b.

Definition tdma_nat_div (a b : Lean.Nat) : Lean.Nat :=
  ImportedFactsTdma.HDiv_hDiv_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedFactsTdma.instHDiv_inst1 Lean.Nat
      ImportedFactsTdma.Nat_instDiv) a b.

Definition tdma_nat_mod (a b : Lean.Nat) : Lean.Nat :=
  ImportedFactsTdma.HMod_hMod_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedFactsTdma.instHMod_inst1 Lean.Nat
      ImportedFactsTdma.Nat_instMod) a b.

Definition tdma_nat_lt (a b : Lean.Nat) : SProp :=
  ImportedFactsTdma.LT_lt_inst1 Lean.Nat
    ImportedFactsTdma.instLTNat a b.

Lemma tdma_nat_add_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR + bR) (tdma_nat_add aL bL).
Proof.
  change (SubNatRel aR aL -> SubNatRel bR bL ->
    SubNatRel (aR + bR) (sub_imported_add aL bL)).
  exact (sub_add_correspondence aR aL bR bL).
Qed.

Lemma tdma_nat_mul_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR * bR) (tdma_nat_mul aL bL).
Proof.
  change (SubNatRel aR aL -> SubNatRel bR bL ->
    SubNatRel (aR * bR) (sub_imported_mul aL bL)).
  exact (sub_mul_correspondence aR aL bR bL).
Qed.

Lemma tdma_nat_sub_zero (a : Lean.Nat) :
  Lean.eq (tdma_nat_sub a Lean.Nat_zero) a.
Proof. exact (@Lean.eq_refl Lean.Nat a). Qed.

Lemma tdma_nat_sub_succ (a b : Lean.Nat) :
  Lean.eq (tdma_nat_sub a (Lean.Nat_succ b))
    (ImportedFactsTdma.Nat_pred (tdma_nat_sub a b)).
Proof.
  exact (@Lean.eq_refl Lean.Nat
    (ImportedFactsTdma.Nat_pred (tdma_nat_sub a b))).
Qed.

Fixpoint tdma_rocq_iterated_pred (a b : nat) : nat :=
  match b with
  | O => a
  | S b' => Nat.pred (tdma_rocq_iterated_pred a b')
  end.

Lemma tdma_rocq_iterated_pred_is_subn (a b : nat) :
  Logic.eq (tdma_rocq_iterated_pred a b) (a - b).
Proof.
  revert a. induction b as [|b IH]; intro a; cbn [tdma_rocq_iterated_pred].
  - rewrite subn0. reflexivity.
  - rewrite (IH a). exact (Logic.eq_sym (subnS a b)).
Qed.

Definition tdma_nat_pred_canonical (n : nat) :
  Lean.eq (ImportedFactsTdma.Nat_pred (sub_nat_to_imported n))
    (sub_nat_to_imported (Nat.pred n)) :=
  match n return
    Lean.eq (ImportedFactsTdma.Nat_pred (sub_nat_to_imported n))
      (sub_nat_to_imported (Nat.pred n))
  with
  | O => @Lean.eq_refl Lean.Nat Lean.Nat_zero
  | S n' => @Lean.eq_refl Lean.Nat (sub_nat_to_imported n')
  end.

Lemma tdma_nat_sub_iterated_pred (a b : nat) :
  Lean.eq
    (tdma_nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (tdma_rocq_iterated_pred a b)).
Proof.
  revert a. induction b as [|b IH]; intro a.
  - exact (tdma_nat_sub_zero (sub_nat_to_imported a)).
  - exact (sub_imported_eq_trans _ _ _
      (tdma_nat_sub_succ _ _)
      (sub_imported_eq_trans _ _ _
        (sub_imported_eq_congr ImportedFactsTdma.Nat_pred _ _ (IH a))
        (tdma_nat_pred_canonical (tdma_rocq_iterated_pred a b)))).
Qed.

Lemma tdma_nat_sub_canonical (a b : nat) :
  Lean.eq
    (tdma_nat_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (a - b)).
Proof.
  exact (sub_imported_eq_trans _ _ _
    (tdma_nat_sub_iterated_pred a b)
    (coq_eq_to_imported_eq _ _
      (f_equal sub_nat_to_imported (tdma_rocq_iterated_pred_is_subn a b)))).
Qed.

Lemma tdma_nat_sub_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR - bR) (tdma_nat_sub aL bL).
Proof.
  intros Ha Hb. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (tdma_nat_sub_canonical aR bR))
    (sub_imported_eq_congr2 tdma_nat_sub _ _ _ _ Ha Hb)).
Qed.

Lemma tdma_nat_lt_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (ltn aR bR)) (tdma_nat_lt aL bL).
Proof.
  change (SubNatRel aR aL -> SubNatRel bR bL ->
    PropSPropRel (is_true (ltn aR bR)) (sub_imported_lt aL bL)).
  exact (sub_nat_lt_correspondence aR aL bR bL).
Qed.

Lemma tdma_nat_eq_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (Logic.eq aR bR) (Lean.eq aL bL).
Proof. exact (sub_nat_eq_correspondence aR aL bR bL). Qed.

Lemma tdma_nat_mod_decoded_canonical (x y : nat) :
  Logic.eq
    (sub_nat_to_rocq
      (tdma_nat_div (sub_nat_to_imported x) (sub_nat_to_imported y)))
    (x %/ y) /\
  Logic.eq
    (sub_nat_to_rocq
      (tdma_nat_mod (sub_nat_to_imported x) (sub_nat_to_imported y)))
    (x %% y).
Proof.
  case Hy: y => [|y'].
  - subst y. split.
    + rewrite divn0.
      (** The zero quotient is used only to identify the Euclidean witness;
          it reduces directly in this imported Nat implementation. *)
      reflexivity.
    + rewrite modn0.
      have H := ImportedFactsTdma.Prosa_Validation_TdmaInterface_tdma_mod_zero
        (sub_nat_to_imported x).
      transitivity (sub_nat_to_rocq (sub_nat_to_imported x)).
      * exact (f_equal sub_nat_to_rocq (imported_eq_to_coq_eq _ _ H)).
      * exact (sub_nat_rocq_roundtrip x).
  - have Hypos : is_true (ltn O y'.+1) by done.
    set xL := sub_nat_to_imported x.
    set yL := sub_nat_to_imported y'.+1.
    set qL := tdma_nat_div xL yL.
    set rL := tdma_nat_mod xL yL.
    have HrLtR : is_true (ltn (sub_nat_to_rocq rL) y'.+1).
    { exact (sprop_to_prop _ _
        (tdma_nat_lt_related (sub_nat_to_rocq rL) rL y'.+1 yL
          (sub_nat_rel_surjective rL) (sub_nat_rel_canonical y'.+1))
        (ImportedFactsTdma.Prosa_Validation_TdmaInterface_tdma_mod_lt
          xL yL
          (prop_to_sprop _ _
            (tdma_nat_lt_related O Lean.Nat_zero y'.+1 yL
              (sub_nat_rel_canonical O) (sub_nat_rel_canonical y'.+1))
            Hypos))). }
    have HdecompR : Logic.eq
        (y'.+1 * sub_nat_to_rocq qL + sub_nat_to_rocq rL) x.
    { exact (sprop_to_prop _ _
        (tdma_nat_eq_related
          (y'.+1 * sub_nat_to_rocq qL + sub_nat_to_rocq rL)
          (tdma_nat_add (tdma_nat_mul yL qL) rL)
          x xL
          (tdma_nat_add_related _ _ _ _
            (tdma_nat_mul_related y'.+1 yL
              (sub_nat_to_rocq qL) qL
              (sub_nat_rel_canonical y'.+1)
              (sub_nat_rel_surjective qL))
            (sub_nat_rel_surjective rL))
          (sub_nat_rel_canonical x))
        (ImportedFactsTdma.Prosa_Validation_TdmaInterface_tdma_div_add_mod
          xL yL)). }
    have Hx : Logic.eq x
        (sub_nat_to_rocq qL * y'.+1 + sub_nat_to_rocq rL).
    { rewrite mulnC. exact (Logic.eq_sym HdecompR). }
    have Hedge : Logic.eq (edivn x y'.+1)
        (sub_nat_to_rocq qL, sub_nat_to_rocq rL).
    { rewrite Hx. exact (@edivn_eq y'.+1 (sub_nat_to_rocq qL)
        (sub_nat_to_rocq rL) HrLtR). }
    have Hq := f_equal (@Datatypes.fst nat nat) Hedge.
    change (Logic.eq (divn x (S y')) (sub_nat_to_rocq qL)) in Hq.
    have Hr := f_equal (@Datatypes.snd nat nat) Hedge.
    change (Logic.eq (Datatypes.snd (edivn x (S y')))
      (sub_nat_to_rocq rL)) in Hr.
    rewrite <- (modn_def x y'.+1) in Hr.
    split; exact (Logic.eq_sym Hq) || exact (Logic.eq_sym Hr).
Qed.

Lemma tdma_nat_mod_canonical (x y : nat) :
  Lean.eq
    (tdma_nat_mod (sub_nat_to_imported x) (sub_nat_to_imported y))
    (sub_nat_to_imported (x %% y)).
Proof.
  have Hdecoded := proj2 (tdma_nat_mod_decoded_canonical x y).
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _
      (sub_nat_imported_roundtrip
        (tdma_nat_mod (sub_nat_to_imported x) (sub_nat_to_imported y))))
    (coq_eq_to_imported_eq _ _ (f_equal sub_nat_to_imported Hdecoded))).
Qed.

Lemma tdma_nat_mod_related xR xL yR yL :
  SubNatRel xR xL -> SubNatRel yR yL ->
  SubNatRel (xR %% yR) (tdma_nat_mod xL yL).
Proof.
  intros Hx Hy. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (tdma_nat_mod_canonical xR yR))
    (sub_imported_eq_congr2 tdma_nat_mod _ _ _ _ Hx Hy)).
Qed.

Lemma tdma_decide_bool_related (bR : bool) (Q : SProp)
    (d : ImportedFactsTdma.Decidable Q) :
  PropSPropRel (is_true bR) Q ->
  ArBoolRel bR (ImportedFactsTdma.Decidable_decide Q d).
Proof.
  intro Hrel. unfold ArBoolRel.
  destruct d as [Hfalse | Htrue]; destruct bR; cbn.
  - exact (match Hfalse (prop_to_sprop _ _ Hrel (Logic.eq_refl true))
      return Lean.eq _ _ with end).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - exact (match ar_coq_false_to_target
      (match sprop_to_prop _ _ Hrel Htrue with end)
      return Lean.eq _ _ with end).
Qed.

Definition tdma_nat_lt_bool (a b : Lean.Nat) :
    ImportedFactsTdma.Bool :=
  ImportedFactsTdma.Decidable_decide
    (tdma_nat_lt a b) (ImportedFactsTdma.Nat_decLt a b).

Lemma tdma_nat_lt_bool_related aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  ArBoolRel (ltn aR bR) (tdma_nat_lt_bool aL bL).
Proof.
  intros Ha Hb. apply tdma_decide_bool_related.
  exact (tdma_nat_lt_related aR aL bR bL Ha Hb).
Qed.

Print Assumptions tdma_nat_sub_related.
Print Assumptions tdma_nat_mod_related.
Print Assumptions tdma_nat_lt_bool_related.
