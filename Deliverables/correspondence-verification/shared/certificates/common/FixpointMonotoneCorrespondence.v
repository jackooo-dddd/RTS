From mathcomp Require Import ssreflect ssrbool eqtype ssrnat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFixpoint.
From FoundationCertificates Require Import PropSPropFoundation LogicalRelation
  SubadditivityNatCorrespondence NatSubCorrespondence
  FixpointBaseCorrespondence.
From prosa Require Import util.rel.

Definition fixpoint_target_le (a b : Lean.Nat) : SProp :=
  ImportedFixpoint.LE_le_inst1 Lean.Nat ImportedFixpoint.instLENat a b.

Definition fixpoint_target_lt (a b : Lean.Nat) : SProp :=
  ImportedFixpoint.LT_lt_inst1 Lean.Nat ImportedFixpoint.instLTNat a b.

Definition fixpoint_target_sub (a b : Lean.Nat) : Lean.Nat :=
  ImportedFixpoint.HSub_hSub_inst7 Lean.Nat Lean.Nat Lean.Nat
    (ImportedFixpoint.instHSub_inst1 Lean.Nat ImportedFixpoint.instSubNat)
    a b.

Definition fixpoint_pred_canonical (n : nat) :
  Lean.eq (ImportedFixpoint.Nat_pred (sub_nat_to_imported n))
    (sub_nat_to_imported (Nat.pred n)) :=
  match n return
      Lean.eq (ImportedFixpoint.Nat_pred (sub_nat_to_imported n))
        (sub_nat_to_imported (Nat.pred n))
  with
  | O => @Lean.eq_refl Lean.Nat Lean.Nat_zero
  | S n' => @Lean.eq_refl Lean.Nat (sub_nat_to_imported n')
  end.

Lemma fixpoint_sub_iterated_pred (a b : nat) :
  Lean.eq
    (fixpoint_target_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (rocq_iterated_pred a b)).
Proof.
  induction b as [|b IH].
  - exact (@Lean.eq_refl Lean.Nat (sub_nat_to_imported a)).
  - exact (sub_imported_eq_trans _ _ _
      (sub_imported_eq_congr ImportedFixpoint.Nat_pred _ _ IH)
      (fixpoint_pred_canonical (rocq_iterated_pred a b))).
Qed.

Lemma fixpoint_sub_canonical (a b : nat) :
  Lean.eq
    (fixpoint_target_sub (sub_nat_to_imported a) (sub_nat_to_imported b))
    (sub_nat_to_imported (a - b)).
Proof.
  exact (sub_imported_eq_trans _ _ _
    (fixpoint_sub_iterated_pred a b)
    (coq_eq_to_imported_eq _ _
      (f_equal sub_nat_to_imported (rocq_iterated_pred_is_subn a b)))).
Qed.

Lemma fixpoint_sub_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  SubNatRel (aR - bR) (fixpoint_target_sub aL bL).
Proof.
  intros Ha Hb. unfold SubNatRel.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_sym _ _ (fixpoint_sub_canonical aR bR))
    (sub_imported_eq_congr2 fixpoint_target_sub _ _ _ _ Ha Hb)).
Qed.

Lemma fixpoint_le_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (leq aR bR)) (fixpoint_target_le aL bL).
Proof. exact (sub_nat_le_correspondence aR aL bR bL). Qed.

Lemma fixpoint_lt_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (ltn aR bR)) (fixpoint_target_lt aL bL).
Proof. exact (sub_nat_lt_correspondence aR aL bR bL). Qed.

Lemma fixpoint_ne_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (aR != bR))
    (ImportedFixpoint.Ne Lean.Nat aL bL).
Proof.
  intros Ha Hb.
  have Heq := sub_nat_eq_correspondence aR aL bR bL Ha Hb.
  apply prop_sprop_rel_intro.
  - intros Hneq HeqL.
    have HeqR := sprop_to_prop _ _ Heq HeqL.
    have HeqB : aR == bR. { apply/eqP. exact HeqR. }
    rewrite HeqB in Hneq.
    have Hfalse : Logic.False. { discriminate Hneq. }
    destruct Hfalse.
  - intro HneL. destruct (aR != bR) eqn:Hneq.
    + exact (strictly_inhabits (Logic.eq_refl true)).
    + have HeqB : aR == bR.
      { destruct (aR == bR) eqn:HeqVal; first reflexivity.
        cbn in Hneq. discriminate Hneq. }
      have HeqR : Logic.eq aR bR. { apply/eqP. exact HeqB. }
      have HeqL := prop_to_sprop _ _ Heq HeqR.
      exact (match HneL HeqL return
        StrictlyInhabited (is_true false) with end).
Qed.

Definition fixpoint_target_decide_le (a b : Lean.Nat) : ImportedFixpoint.Bool :=
  ImportedFixpoint.Decidable_decide (fixpoint_target_le a b)
    (ImportedFixpoint.Nat_decLe a b).

Definition fixpoint_false_elim (Q : SProp)
    (H : ImportedFixpoint.False) : Q := match H return Q with end.

Inductive FixpointTrue : SProp := fixpoint_true_intro.

Definition fixpoint_bool_false_ne_true
    (H : Lean.eq ImportedFixpoint.Bool_false
      ImportedFixpoint.Bool_true) : ImportedFixpoint.False :=
  match H in Lean.eq _ z return
    match z with
    | ImportedFixpoint.Bool_false => FixpointTrue
    | ImportedFixpoint.Bool_true => ImportedFixpoint.False
    end
  with Lean.eq_refl => fixpoint_true_intro end.

Definition fixpoint_decide_forward (P : SProp)
    (d : ImportedFixpoint.Decidable P) :
    P -> Lean.eq (ImportedFixpoint.Decidable_decide P d)
      ImportedFixpoint.Bool_true :=
  match d as d0 return
      P -> Lean.eq (ImportedFixpoint.Decidable_decide P d0)
        ImportedFixpoint.Bool_true
  with
  | ImportedFixpoint.Decidable_isTrue H =>
      fun _ => @Lean.eq_refl ImportedFixpoint.Bool
        ImportedFixpoint.Bool_true
  | ImportedFixpoint.Decidable_isFalse H =>
      fun p => fixpoint_false_elim _ (H p)
  end.

Definition fixpoint_decide_backward (P : SProp)
    (d : ImportedFixpoint.Decidable P) :
    Lean.eq (ImportedFixpoint.Decidable_decide P d)
      ImportedFixpoint.Bool_true -> P :=
  match d as d0 return
      Lean.eq (ImportedFixpoint.Decidable_decide P d0)
        ImportedFixpoint.Bool_true -> P
  with
  | ImportedFixpoint.Decidable_isTrue H => fun _ => H
  | ImportedFixpoint.Decidable_isFalse H =>
      fun Heq => fixpoint_false_elim _
        (fixpoint_bool_false_ne_true Heq)
  end.

Lemma fixpoint_decide_le_true_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (leq aR bR))
    (Lean.eq (fixpoint_target_decide_le aL bL)
      ImportedFixpoint.Bool_true).
Proof.
  intros Ha Hb.
  have Hle : PropSPropRel (is_true (leq aR bR))
      (fixpoint_target_le aL bL) :=
    sub_nat_le_correspondence aR aL bR bL Ha Hb.
  apply prop_sprop_rel_intro.
  - intro HR. apply fixpoint_decide_forward.
    exact (prop_to_sprop _ _ Hle HR).
  - intro HL. apply strictly_inhabits.
    exact (sprop_to_prop _ _ Hle
      (fixpoint_decide_backward _ _ HL)).
Qed.

Definition fixpoint_target_monotone (f : Lean.Nat -> Lean.Nat) : SProp :=
  ImportedFixpoint.Prosa_Util_Rel_monotone_inst1 Lean.Nat
    fixpoint_target_decide_le f.

Lemma fixpoint_monotone_correspondence
    (fR : nat -> nat) (fL : Lean.Nat -> Lean.Nat) :
  SubNatFunRel fR fL ->
  PropSPropRel (prosa.util.rel.monotone leq fR)
    (fixpoint_target_monotone fL).
Proof.
  intro Hf. apply prop_sprop_rel_intro.
  - intros HR xL yL HxyL.
    set (xR := sub_nat_to_rocq xL).
    set (yR := sub_nat_to_rocq yL).
    have Hx : SubNatRel xR xL := sub_nat_rel_surjective xL.
    have Hy : SubNatRel yR yL := sub_nat_rel_surjective yL.
    have HxyR := sprop_to_prop _ _
      (fixpoint_decide_le_true_correspondence _ _ _ _ Hx Hy) HxyL.
    have Hfx := Hf _ _ Hx.
    have Hfy := Hf _ _ Hy.
    exact (prop_to_sprop _ _
      (fixpoint_decide_le_true_correspondence _ _ _ _ Hfx Hfy)
      (HR xR yR HxyR)).
  - intro HL. apply strictly_inhabits. intros xR yR HxyR.
    have Hx := sub_nat_rel_canonical xR.
    have Hy := sub_nat_rel_canonical yR.
    have HxyL := prop_to_sprop _ _
      (fixpoint_decide_le_true_correspondence _ _ _ _ Hx Hy) HxyR.
    have Hfx := Hf _ _ Hx.
    have Hfy := Hf _ _ Hy.
    exact (sprop_to_prop _ _
      (fixpoint_decide_le_true_correspondence _ _ _ _ Hfx Hfy)
      (HL _ _ HxyL)).
Qed.

Print Assumptions fixpoint_decide_le_true_correspondence.
Print Assumptions fixpoint_monotone_correspondence.
