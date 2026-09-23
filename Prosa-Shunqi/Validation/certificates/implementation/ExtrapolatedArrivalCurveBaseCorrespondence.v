From mathcomp Require Import ssreflect ssrbool ssrnat seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedExtrapolatedArrivalCurveBase.
From FoundationCertificates Require Import SubadditivityNatCorrespondence.
Require Import OfficialExtrapolatedArrivalCurveBase.

(** An operation-level representation relation for the actual imported
    Lean product/list constructors. Source sequence order and multiplicity
    are retained. *)
Definition eac_imported_step (p : nat * nat) :
    ImportedExtrapolatedArrivalCurveBase.Prod_inst3 Lean.Nat Lean.Nat :=
  match p with
  | (t, n) => ImportedExtrapolatedArrivalCurveBase.Prod_mk_inst3
      Lean.Nat Lean.Nat (sub_nat_to_imported t) (sub_nat_to_imported n)
  end.

Fixpoint eac_imported_steps (xs : seq (nat * nat)) :
    ImportedExtrapolatedArrivalCurveBase.List_inst1
      (ImportedExtrapolatedArrivalCurveBase.Prod_inst3 Lean.Nat Lean.Nat) :=
  match xs with
  | [::] => ImportedExtrapolatedArrivalCurveBase.List_nil_inst1 _
  | x :: tail => ImportedExtrapolatedArrivalCurveBase.List_cons_inst1 _
      (eac_imported_step x) (eac_imported_steps tail)
  end.

Fixpoint eac_imported_times (xs : seq nat) :
    ImportedExtrapolatedArrivalCurveBase.List_inst1 Lean.Nat :=
  match xs with
  | [::] => ImportedExtrapolatedArrivalCurveBase.List_nil_inst1 _
  | x :: tail => ImportedExtrapolatedArrivalCurveBase.List_cons_inst1 _
      (sub_nat_to_imported x) (eac_imported_times tail)
  end.

Definition eac_imported_prefix
    (p : OfficialExtrapolatedArrivalCurveBase.ArrivalCurvePrefix) :
    ImportedExtrapolatedArrivalCurveBase.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix :=
  match p with
  | (h, steps) => ImportedExtrapolatedArrivalCurveBase.Prod_mk_inst3
      Lean.Nat _ (sub_nat_to_imported h) (eac_imported_steps steps)
  end.

Definition EacPrefixRel (pR : OfficialExtrapolatedArrivalCurveBase.ArrivalCurvePrefix)
    (pL : ImportedExtrapolatedArrivalCurveBase.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_ArrivalCurvePrefix) : SProp :=
  Lean.eq (eac_imported_prefix pR) pL.

Lemma eac_inter_arrival_to_prefix_correspondence :
  forall pR pL, SubNatRel pR pL ->
    EacPrefixRel
      (OfficialExtrapolatedArrivalCurveBase.inter_arrival_to_prefix pR)
      (ImportedExtrapolatedArrivalCurveBase.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_inter_arrival_to_prefix pL).
Proof.
  intros pR pL Hp.
  destruct Hp.
  exact (@Lean.eq_refl _ _).
Qed.

Lemma eac_horizon_of_correspondence :
  forall pR pL, EacPrefixRel pR pL ->
    SubNatRel
      (OfficialExtrapolatedArrivalCurveBase.horizon_of pR)
      (ImportedExtrapolatedArrivalCurveBase.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_horizon_of pL).
Proof.
  intros [h steps] pL Hp.
  destruct Hp.
  exact (@Lean.eq_refl _ _).
Qed.

Lemma eac_steps_of_correspondence :
  forall pR pL, EacPrefixRel pR pL ->
    Lean.eq
      (eac_imported_steps
        (OfficialExtrapolatedArrivalCurveBase.steps_of pR))
      (ImportedExtrapolatedArrivalCurveBase.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_steps_of pL).
Proof.
  intros [h steps] pL Hp.
  destruct Hp.
  exact (@Lean.eq_refl _ _).
Qed.

Lemma eac_time_steps_of_correspondence :
  forall pR pL, EacPrefixRel pR pL ->
    Lean.eq
      (eac_imported_times
        (OfficialExtrapolatedArrivalCurveBase.time_steps_of pR))
      (ImportedExtrapolatedArrivalCurveBase.Prosa_Implementation_Definitions_ExtrapolatedArrivalCurve_time_steps_of pL).
Proof.
  intros [h steps] pL Hp.
  destruct Hp.
  induction steps as [|[t n] tail IH]; cbn.
  - exact (@Lean.eq_refl _ _).
  - exact (sub_imported_eq_congr
      (ImportedExtrapolatedArrivalCurveBase.List_cons_inst1 Lean.Nat
        (sub_nat_to_imported t)) _ _ IH).
Qed.

Print Assumptions eac_inter_arrival_to_prefix_correspondence.
Print Assumptions eac_horizon_of_correspondence.
Print Assumptions eac_steps_of_correspondence.
Print Assumptions eac_time_steps_of_correspondence.
