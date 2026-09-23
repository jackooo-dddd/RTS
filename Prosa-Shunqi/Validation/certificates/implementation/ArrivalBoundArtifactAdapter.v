From LeanImport Require Import Lean.
From FoundationImported Require Import
  ImportedExtrapolatedArrivalCurve ImportedArrivalBound.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.
From ImplementationCertificates Require Import
  ExtrapolatedArrivalCurveFullCorrespondence.
Require Import OfficialExtrapolatedArrivalCurve.

(** Artifact-local datatype adapter.  The same compiled Lean prefix type is
    represented by distinct Rocq constants in the two independent exports.
    This converter reconnects it to the already certified Rank 33 prefix
    relation without duplicating the source seq/List proof. *)
Definition ab_to_eac_step
    (p : ImportedArrivalBound.Prod_inst3 Lean.Nat Lean.Nat) :
    ImportedExtrapolatedArrivalCurve.Prod_inst3 Lean.Nat Lean.Nat :=
  match p with
  | ImportedArrivalBound.Prod_mk_inst3 a b =>
      ImportedExtrapolatedArrivalCurve.Prod_mk_inst3 Lean.Nat Lean.Nat a b
  end.

Definition eac_to_ab_step
    (p : ImportedExtrapolatedArrivalCurve.Prod_inst3 Lean.Nat Lean.Nat) :
    ImportedArrivalBound.Prod_inst3 Lean.Nat Lean.Nat :=
  match p with
  | ImportedExtrapolatedArrivalCurve.Prod_mk_inst3 a b =>
      ImportedArrivalBound.Prod_mk_inst3 Lean.Nat Lean.Nat a b
  end.

Fixpoint ab_to_eac_steps
    (xs : ImportedArrivalBound.List_inst1
      (ImportedArrivalBound.Prod_inst3 Lean.Nat Lean.Nat)) :
    ImportedExtrapolatedArrivalCurve.List_inst1
      (ImportedExtrapolatedArrivalCurve.Prod_inst3 Lean.Nat Lean.Nat) :=
  match xs with
  | ImportedArrivalBound.List_nil_inst1 =>
      ImportedExtrapolatedArrivalCurve.List_nil_inst1 _
  | ImportedArrivalBound.List_cons_inst1 x tail =>
      ImportedExtrapolatedArrivalCurve.List_cons_inst1 _
        (ab_to_eac_step x) (ab_to_eac_steps tail)
  end.

Fixpoint eac_to_ab_steps
    (xs : ImportedExtrapolatedArrivalCurve.List_inst1
      (ImportedExtrapolatedArrivalCurve.Prod_inst3 Lean.Nat Lean.Nat)) :
    ImportedArrivalBound.List_inst1
      (ImportedArrivalBound.Prod_inst3 Lean.Nat Lean.Nat) :=
  match xs with
  | ImportedExtrapolatedArrivalCurve.List_nil_inst1 =>
      ImportedArrivalBound.List_nil_inst1 _
  | ImportedExtrapolatedArrivalCurve.List_cons_inst1 x tail =>
      ImportedArrivalBound.List_cons_inst1 _
        (eac_to_ab_step x) (eac_to_ab_steps tail)
  end.

Definition ab_to_eac_prefix
    (p : ImportedArrivalBound.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix) :
    ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix :=
  match p with
  | ImportedArrivalBound.Prod_mk_inst3 h steps =>
      ImportedExtrapolatedArrivalCurve.Prod_mk_inst3 Lean.Nat _ h
        (ab_to_eac_steps steps)
  end.

Definition eac_to_ab_prefix
    (p : ImportedExtrapolatedArrivalCurve.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix) :
    ImportedArrivalBound.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix :=
  match p with
  | ImportedExtrapolatedArrivalCurve.Prod_mk_inst3 h steps =>
      ImportedArrivalBound.Prod_mk_inst3 Lean.Nat _ h
        (eac_to_ab_steps steps)
  end.

Lemma ab_step_roundtrip (p : ImportedArrivalBound.Prod_inst3 Lean.Nat Lean.Nat) :
  Logic.eq (eac_to_ab_step (ab_to_eac_step p)) p.
Proof. destruct p. reflexivity. Qed.

Lemma eac_step_roundtrip
    (p : ImportedExtrapolatedArrivalCurve.Prod_inst3 Lean.Nat Lean.Nat) :
  Logic.eq (ab_to_eac_step (eac_to_ab_step p)) p.
Proof. destruct p. reflexivity. Qed.

Lemma ab_steps_roundtrip xs :
  Logic.eq (eac_to_ab_steps (ab_to_eac_steps xs)) xs.
Proof.
  induction xs as [|x tail IH]; simpl.
  - reflexivity.
  - rewrite (ab_step_roundtrip x) IH. reflexivity.
Qed.

Lemma eac_steps_roundtrip xs :
  Logic.eq (ab_to_eac_steps (eac_to_ab_steps xs)) xs.
Proof.
  induction xs as [|x tail IH]; simpl.
  - reflexivity.
  - rewrite (eac_step_roundtrip x) IH. reflexivity.
Qed.

Lemma ab_prefix_roundtrip p :
  Logic.eq (eac_to_ab_prefix (ab_to_eac_prefix p)) p.
Proof.
  destruct p as [h steps].
  unfold eac_to_ab_prefix, ab_to_eac_prefix. simpl.
  rewrite (ab_steps_roundtrip steps). reflexivity.
Qed.

Lemma eac_prefix_roundtrip p :
  Logic.eq (ab_to_eac_prefix (eac_to_ab_prefix p)) p.
Proof.
  destruct p as [h steps].
  unfold ab_to_eac_prefix, eac_to_ab_prefix. simpl.
  rewrite (eac_steps_roundtrip steps). reflexivity.
Qed.

Definition ab_prefix_from_source pR :=
  eac_to_ab_prefix (eac_imported_prefix pR).

Definition ab_prefix_to_source pL :=
  eac_rocq_prefix (ab_to_eac_prefix pL).

Lemma ab_prefix_source_roundtrip pR :
  Logic.eq (ab_prefix_to_source (ab_prefix_from_source pR)) pR.
Proof.
  unfold ab_prefix_to_source, ab_prefix_from_source.
  rewrite (eac_prefix_roundtrip (eac_imported_prefix pR)).
  exact (eac_prefix_rocq_roundtrip pR).
Qed.

Lemma ab_prefix_target_roundtrip pL :
  Lean.eq (ab_prefix_from_source (ab_prefix_to_source pL)) pL.
Proof.
  unfold ab_prefix_from_source, ab_prefix_to_source.
  exact (sub_imported_eq_trans _ _ _
    (sub_imported_eq_congr eac_to_ab_prefix _ _
      (eac_prefix_imported_roundtrip (ab_to_eac_prefix pL)))
    (coq_eq_to_imported_eq _ _ (ab_prefix_roundtrip pL))).
Qed.

Print Assumptions ab_prefix_source_roundtrip.
Print Assumptions ab_prefix_target_roundtrip.
