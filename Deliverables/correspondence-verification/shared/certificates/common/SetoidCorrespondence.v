From Stdlib Require Import Basics Setoid Morphisms.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSetoid ImportedSubadditivity.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.
Require Import prosa.util.setoid.

Inductive StFalse : SProp := .

Definition st_false_elim (Q : SProp) (H : StFalse) : Q :=
  match H return Q with end.

Definition st_false_to_strict (H : StFalse) :
    StrictlyInhabited Logic.False := match H with end.

Definition st_coq_false_to_target (H : Logic.False) :
    StFalse := match H return StFalse with end.

Inductive StTrue : SProp := st_true_intro.

Definition st_false_ne_true
    (H : Lean.eq ImportedSetoid.Bool_false ImportedSetoid.Bool_true) :
    StFalse :=
  match H in Lean.eq _ z return
    match z with
    | ImportedSetoid.Bool_false => StTrue
    | ImportedSetoid.Bool_true => StFalse
    end
  with
  | Lean.eq_refl => st_true_intro
  end.

Definition st_bool_to_imported (b : bool) : ImportedSetoid.Bool :=
  match b with
  | true => ImportedSetoid.Bool_true
  | false => ImportedSetoid.Bool_false
  end.

Definition st_bool_to_rocq (b : ImportedSetoid.Bool) : bool :=
  match b with
  | ImportedSetoid.Bool_true => true
  | ImportedSetoid.Bool_false => false
  end.

Definition StBoolRel (bR : bool) (bL : ImportedSetoid.Bool) : SProp :=
  Lean.eq (st_bool_to_imported bR) bL.

Lemma st_bool_source_roundtrip (b : bool) :
  Logic.eq (st_bool_to_rocq (st_bool_to_imported b)) b.
Proof. destruct b; reflexivity. Qed.

Lemma st_bool_target_roundtrip (b : ImportedSetoid.Bool) :
  Lean.eq (st_bool_to_imported (st_bool_to_rocq b)) b.
Proof. destruct b; exact (@Lean.eq_refl _ _). Qed.

Lemma st_bool_truth_correspondence bR bL : StBoolRel bR bL ->
  PropSPropRel (is_true bR)
    (Lean.eq bL ImportedSetoid.Bool_true).
Proof.
  intro Hb. apply prop_sprop_rel_intro.
  - intro Htrue. destruct bR; cbn in Htrue.
    + exact (sub_imported_eq_sym _ _ Hb).
    + discriminate Htrue.
  - intro HL. apply strictly_inhabits.
    destruct bR; cbn.
    + reflexivity.
    + exact (False_rect _ (interpret_strict Logic.False
        (st_false_to_strict (st_false_ne_true
          (sub_imported_eq_trans _ _ _ Hb HL))))).
Qed.

Lemma st_imp_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P -> Q) (PL -> QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros H pL. apply (prop_to_sprop _ _ HQ).
    apply H. exact (sprop_to_prop _ _ HP pL).
  - intro H. apply strictly_inhabits. intro p.
    apply (sprop_to_prop _ _ HQ).
    exact (H (prop_to_sprop _ _ HP p)).
Qed.

Lemma st_iff_correspondence (P Q : Prop) (PL QL : SProp) :
  PropSPropRel P PL -> PropSPropRel Q QL ->
  PropSPropRel (P <-> Q) (ImportedSetoid.Iff PL QL).
Proof.
  intros HP HQ. apply prop_sprop_rel_intro.
  - intros [HPQ HQP]. exact (ImportedSetoid.Iff_intro _ _
      (fun p => prop_to_sprop _ _ HQ (HPQ (sprop_to_prop _ _ HP p)))
      (fun q => prop_to_sprop _ _ HP (HQP (sprop_to_prop _ _ HQ q)))).
  - intro H. apply strictly_inhabits. split.
    + intro p. apply (sprop_to_prop _ _ HQ).
      exact (ImportedSetoid.mp _ _ H (prop_to_sprop _ _ HP p)).
    + intro q. apply (sprop_to_prop _ _ HP).
      exact (ImportedSetoid.mpr _ _ H (prop_to_sprop _ _ HQ q)).
Qed.

Lemma st_implb_truth (a b : bool) :
  is_true (implb a b) <-> (is_true a -> is_true b).
Proof. split; first by move/implyP. by move=> H; apply/implyP. Qed.

Definition st_target_leb (a b : ImportedSetoid.Bool) : SProp :=
  ImportedSetoid.Prosa_Util_Setoid_leb a b.

(** Constructor-level correspondence for the actual source and imported
    inductives. *)
Lemma st_leb_correspondence aR aL bR bL :
  StBoolRel aR aL -> StBoolRel bR bL ->
  PropSPropRel (prosa.util.setoid.leb aR bR) (st_target_leb aL bL).
Proof.
  intros Ha Hb. apply prop_sprop_rel_intro.
  - intros [Himpl]. apply ImportedSetoid.Prosa_Util_Setoid_leb_intro.
    intro Hat.
    have HaR := sprop_to_prop _ _ (st_bool_truth_correspondence aR aL Ha) Hat.
    have HbR := (proj1 (st_implb_truth aR bR) Himpl) HaR.
    exact (prop_to_sprop _ _ (st_bool_truth_correspondence bR bL Hb) HbR).
  - intro Htarget. destruct Htarget as [Himpl].
    apply strictly_inhabits. apply prosa.util.setoid.Leb.
    apply (proj2 (st_implb_truth aR bR)). intro HaR.
    have HaL := prop_to_sprop _ _ (st_bool_truth_correspondence aR aL Ha) HaR.
    have HbL := Himpl HaL.
    exact (sprop_to_prop _ _ (st_bool_truth_correspondence bR bL Hb) HbL).
Qed.

Definition st_target_le (a b : Lean.Nat) : SProp :=
  ImportedSetoid.LE_le_inst1 Lean.Nat ImportedSetoid.instLENat a b.

Lemma st_nat_bool_le_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel (is_true (leq aR bR)) (st_target_le aL bL).
Proof.
  intros Ha Hb. change (PropSPropRel (is_true (leq aR bR))
    (Lean.Nat_le aL bL)).
  exact (sub_nat_le_correspondence aR aL bR bL Ha Hb).
Qed.

Lemma st_nat_coq_le_correspondence aR aL bR bL :
  SubNatRel aR aL -> SubNatRel bR bL ->
  PropSPropRel ((aR <= bR)%coq_nat) (st_target_le aL bL).
Proof.
  intros Ha Hb. apply prop_sprop_rel_intro.
  - intro Hle. apply (prop_to_sprop _ _
      (st_nat_bool_le_correspondence aR aL bR bL Ha Hb)).
    exact (introT leP Hle).
  - intro Hle. apply strictly_inhabits. apply (elimT leP).
    exact (sprop_to_prop _ _
      (st_nat_bool_le_correspondence aR aL bR bL Ha Hb) Hle).
Qed.

Print Assumptions st_bool_truth_correspondence.
Print Assumptions st_leb_correspondence.
Print Assumptions st_nat_coq_le_correspondence.
