From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSwap ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence.

Definition swap_coq_false_to_target (H : Logic.False) :
    ImportedSwap.False := match H with end.

Definition swap_decidable_eq (T : eqType) : ImportedSwap.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H => ImportedSwap.Decidable_isTrue (Lean.eq x y)
        (coq_eq_to_imported_eq x y H)
    | ReflectF H => ImportedSwap.Decidable_isFalse (Lean.eq x y)
        (fun HL => swap_coq_false_to_target
          (H (imported_eq_to_coq_eq x y HL)))
    end.

Definition swap_bool_to_rocq (b : ImportedSwap.Bool) : bool :=
  match b with
  | ImportedSwap.Bool_true => true
  | ImportedSwap.Bool_false => false
  end.

Definition swap_bool_from_rocq (b : bool) : ImportedSwap.Bool :=
  if b then ImportedSwap.Bool_true else ImportedSwap.Bool_false.

Definition swap_nat_beq (a b : Lean.Nat) : ImportedSwap.Bool :=
  ImportedSwap.BEq_beq_inst1 Lean.Nat
    (ImportedSwap.instBEqOfDecidableEq_inst1 Lean.Nat
      ImportedSwap.instDecidableEqNat) a b.

Lemma swap_nat_beq_related (aR bR : nat) (aL bL : Lean.Nat) :
  SubNatRel aR aL -> SubNatRel bR bL ->
  Lean.eq (swap_bool_from_rocq (aR == bR)) (swap_nat_beq aL bL).
Proof.
  intros Ha Hb.
  have Hrel := sub_nat_eq_correspondence aR aL bR bL Ha Hb.
  destruct (aR == bR) eqn:E.
  - have Hsource : Logic.eq aR bR by apply/eqP; exact E.
    have Htarget := prop_to_sprop _ _ Hrel Hsource.
    unfold swap_bool_from_rocq, swap_nat_beq.
    change (Lean.eq ImportedSwap.Bool_true
      (ImportedSwap.Decidable_decide (Lean.eq aL bL)
        (ImportedSwap.Nat_decEq aL bL))).
    destruct (ImportedSwap.Nat_decEq aL bL) as [Hfalse|Htrue].
    + destruct (Hfalse Htarget).
    + exact (@Lean.eq_refl ImportedSwap.Bool ImportedSwap.Bool_true).
  - have Hneq : Logic.eq aR bR -> Logic.False.
    { intro H; subst bR. rewrite eqxx in E. discriminate. }
    unfold swap_bool_from_rocq, swap_nat_beq.
    change (Lean.eq ImportedSwap.Bool_false
      (ImportedSwap.Decidable_decide (Lean.eq aL bL)
        (ImportedSwap.Nat_decEq aL bL))).
    destruct (ImportedSwap.Nat_decEq aL bL) as [Hfalse|Htrue].
    + exact (@Lean.eq_refl ImportedSwap.Bool ImportedSwap.Bool_false).
    + exfalso. exact (Hneq (sprop_to_prop _ _ Hrel Htrue)).
Qed.
