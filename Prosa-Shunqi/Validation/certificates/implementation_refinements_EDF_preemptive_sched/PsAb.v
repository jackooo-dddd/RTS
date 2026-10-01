(* Re-bound copy of the accepted certificates/implementation_facts_job_constructor/AbCorrespondence.v: modules renamed (ImportedFactsJobConstructor=ImportedRefEDFPSched,EacFullCorrespondence=PsEac,AbCorrespondence=PsAb,ImplTaskCorrespondence=PsImplTask,JcListOps=PsListOps), its statement
   correspondences dropped (their statement-only targets are not part of this export), and the commands that mention
   constants absent from this export dropped (the file's report lists them).  Every kept command is unchanged. *)
(* Copy of the accepted certificates/implementation_definitions_task/PsAb.v, re-bound to this export; only the
   imported module name differs, and the four reflection-view blocks are dropped (the Lean BoolReflect family and the
   eqn_task/eqn_job statements are not targets of this export); every kept block is unchanged. *)
(* Copy of the accepted certificates/implementation/ArrivalBoundCorrespondence.v, re-bound to this export: the
   source side is the pinned arrival_bound.v (compiled under its Rocq 9.3 import-compatibility patch) instead of
   the accepted definition-extracted OfficialArrivalBound signature; the adapter between the two earlier separate
   exports is replaced by the prefix maps of PsEac (one export here); the Lean-eqdef Boolean
   correspondence and the eqn_task_arrivals_bound statement correspondence (not part of this file) are dropped,
   as are the Print Assumptions commands. *)
From mathcomp Require Import ssreflect ssrbool eqtype ssrnat seq.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedRefEDFPSched.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence.
From FoundationCertificates Require Import PsEac.
From prosa Require Import implementation.definitions.arrival_bound.

(** The prefix type is the extrapolated-curve prefix of this same export, so the accepted adapter between the
    two separate earlier exports is replaced by the EAC prefix maps and roundtrips. *)
Definition ab_prefix_from_source pR := eac_imported_prefix pR.
Definition ab_prefix_to_source pL := eac_rocq_prefix pL.
Lemma ab_prefix_source_roundtrip pR :
  Logic.eq (ab_prefix_to_source (ab_prefix_from_source pR)) pR.
Proof. exact (eac_prefix_rocq_roundtrip pR). Qed.
Lemma ab_prefix_target_roundtrip pL :
  Lean.eq (ab_prefix_from_source (ab_prefix_to_source pL)) pL.
Proof. exact (eac_prefix_imported_roundtrip pL). Qed.

Definition AbSource := prosa.implementation.definitions.arrival_bound.task_arrivals_bound.
Definition AbTarget :=
  ImportedRefEDFPSched.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound.

Definition ab_export_bound (xR : AbSource) : AbTarget :=
  match xR with
  | prosa.implementation.definitions.arrival_bound.Periodic n =>
      ImportedRefEDFPSched.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Periodic
        (sub_nat_to_imported n)
  | prosa.implementation.definitions.arrival_bound.Sporadic n =>
      ImportedRefEDFPSched.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Sporadic
        (sub_nat_to_imported n)
  | prosa.implementation.definitions.arrival_bound.ArrivalPrefix p =>
      ImportedRefEDFPSched.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_ArrivalPrefix
        (ab_prefix_from_source p)
  end.

Definition ab_import_bound (xL : AbTarget) : AbSource :=
  match xL with
  | ImportedRefEDFPSched.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Periodic n =>
      prosa.implementation.definitions.arrival_bound.Periodic (sub_nat_to_rocq n)
  | ImportedRefEDFPSched.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Sporadic n =>
      prosa.implementation.definitions.arrival_bound.Sporadic (sub_nat_to_rocq n)
  | ImportedRefEDFPSched.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_ArrivalPrefix p =>
      prosa.implementation.definitions.arrival_bound.ArrivalPrefix
        (ab_prefix_to_source p)
  end.

Definition AbRel (xR : AbSource) (xL : AbTarget) : SProp :=
  Lean.eq (ab_export_bound xR) xL.

Lemma ab_source_roundtrip xR :
  Logic.eq (ab_import_bound (ab_export_bound xR)) xR.
Proof.
  destruct xR as [n|n|p]; simpl.
  - rewrite (sub_nat_rocq_roundtrip n). reflexivity.
  - rewrite (sub_nat_rocq_roundtrip n). reflexivity.
  - rewrite (ab_prefix_source_roundtrip p). reflexivity.
Qed.

Lemma ab_target_roundtrip xL :
  AbRel (ab_import_bound xL) xL.
Proof.
  destruct xL as [n|n|p]; simpl.
  - exact (sub_imported_eq_congr
      ImportedRefEDFPSched.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Periodic
      _ _ (sub_nat_imported_roundtrip n)).
  - exact (sub_imported_eq_congr
      ImportedRefEDFPSched.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Sporadic
      _ _ (sub_nat_imported_roundtrip n)).
  - exact (sub_imported_eq_congr
      ImportedRefEDFPSched.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_ArrivalPrefix
      _ _ (ab_prefix_target_roundtrip p)).
Qed.

Lemma ab_source_constructor_periodic nR nL :
  SubNatRel nR nL ->
  AbRel (prosa.implementation.definitions.arrival_bound.Periodic nR)
    (ImportedRefEDFPSched.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Periodic nL).
Proof.
  intro Hn. exact (sub_imported_eq_congr
    ImportedRefEDFPSched.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Periodic
    _ _ Hn).
Qed.

Lemma ab_source_constructor_sporadic nR nL :
  SubNatRel nR nL ->
  AbRel (prosa.implementation.definitions.arrival_bound.Sporadic nR)
    (ImportedRefEDFPSched.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Sporadic nL).
Proof.
  intro Hn. exact (sub_imported_eq_congr
    ImportedRefEDFPSched.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_Sporadic
    _ _ Hn).
Qed.

Lemma ab_source_constructor_prefix pR pL :
  Lean.eq (ab_prefix_from_source pR) pL ->
  AbRel (prosa.implementation.definitions.arrival_bound.ArrivalPrefix pR)
    (ImportedRefEDFPSched.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_ArrivalPrefix pL).
Proof.
  intro Hp. exact (sub_imported_eq_congr
    ImportedRefEDFPSched.Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound_ArrivalPrefix
    _ _ Hp).
Qed.

(** Proved from the byte-identical source definition, not from the source
    [eqn_task_arrivals_bound] theorem proof. *)
Lemma ab_source_eqdef_iff (x y : AbSource) :
  is_true (prosa.implementation.definitions.arrival_bound.task_arrivals_bound_eqdef x y)
    <-> Logic.eq x y.
Proof.
  destruct x as [a|a|a]; destruct y as [b|b|b]; simpl;
    try (split; [intro H; discriminate H | intro H; discriminate H]);
    split.
  - move/eqP=>H. subst. reflexivity.
  - intro H. inversion H; subst. apply/eqP. reflexivity.
  - move/eqP=>H. subst. reflexivity.
  - intro H. inversion H; subst. apply/eqP. reflexivity.
  - move/eqP=>H. subst. reflexivity.
  - intro H. inversion H; subst. apply/eqP. reflexivity.
Qed.

Lemma ab_equality_correspondence xR xL yR yL :
  AbRel xR xL -> AbRel yR yL ->
  PropSPropRel (Logic.eq xR yR) (Lean.eq xL yL).
Proof.
  intros Hx Hy. apply prop_sprop_rel_intro.
  - intro Hxy. destruct Hxy. destruct Hx. destruct Hy.
    exact (@Lean.eq_refl _ _).
  - intro Hxy. apply strictly_inhabits.
    destruct Hx. destruct Hy.
    have Hdecoded := f_equal ab_import_bound
      (imported_eq_to_coq_eq _ _ Hxy).
    rewrite (ab_source_roundtrip xR) (ab_source_roundtrip yR)
      in Hdecoded.
    exact Hdecoded.
Qed.

Definition ab_bool_to_imported (b : bool) : ImportedRefEDFPSched.Bool :=
  match b with
  | true => ImportedRefEDFPSched.Bool_true
  | false => ImportedRefEDFPSched.Bool_false
  end.

Definition AbBoolRel (bR : bool) (bL : ImportedRefEDFPSched.Bool) : SProp :=
  Lean.eq (ab_bool_to_imported bR) bL.

Definition ab_target_false_elim (Q : SProp)
    (H : ImportedRefEDFPSched.False) : Q :=
  match H return Q with end.

Definition ab_rocq_false_to_target (H : Logic.False) :
    ImportedRefEDFPSched.False :=
  match H return ImportedRefEDFPSched.False with end.

Lemma ab_decide_bool_correspondence (bR : bool) (Q : SProp)
    (d : ImportedRefEDFPSched.Decidable Q) :
  PropSPropRel (is_true bR) Q ->
  AbBoolRel bR (ImportedRefEDFPSched.Decidable_decide Q d).
Proof.
  intro Hrel. unfold AbBoolRel.
  destruct d as [Hfalse | Htrue]; destruct bR; cbn.
  - exact (ab_target_false_elim _
      (Hfalse (prop_to_sprop _ _ Hrel (Logic.eq_refl true)))).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - exact (ab_target_false_elim _ (ab_rocq_false_to_target
      (match sprop_to_prop _ _ Hrel Htrue with end))).
Qed.

(** The source [Equality.axiom] is an informative [reflect] view in [Type].
    The target has a separately imported [BoolReflect] family.  Both maps
    preserve the constructors and do not invoke either public theorem proof. *)
Definition ab_bool_from_imported (b : ImportedRefEDFPSched.Bool) : bool :=
  match b with
  | ImportedRefEDFPSched.Bool_true => true
  | ImportedRefEDFPSched.Bool_false => false
  end.
