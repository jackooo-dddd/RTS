(* Re-bound copy of accepted .work/experiments/analysis_abstract_definitions/certificates/ServiceScheduleOperations.v for the busy_sbf artifact; only the imported module name differs. *)
(** Artifact-local replay: the only source rewrite is the imported module identity.
    Accepted producer source SHA-256: 0d6a3b5b83724244e819e258e5735e8e8ff1a4ab2f0b67cdee6fdff53aac7d4f.
    Substitution: ImportedService -> ImportedBusySbf.
    This file must be recompiled and audited by Rocq. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq
  fintype bigop.
From prosa Require Import behavior.schedule.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedBusySbf ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence ServiceBaseAdapter
  ServiceNatBoolOperations ServiceIntervalOperations.

(** Artifact-local instantiation of the already-certified ProcessorState
observational relation.  The reusable proof structure is the Schedule
certificate; this adapter binds it to the Nat/Bool/List constructors present
in the actual Service export. *)

Definition svc_target_list_sum
    (xs : ImportedBusySbf.List_inst1 Lean.Nat) : Lean.Nat :=
  ImportedBusySbf.List_sum_inst1 Lean.Nat ImportedBusySbf.instAddNat
    (ImportedBusySbf.MulZeroClass_toZero_inst1 Lean.Nat
      ImportedBusySbf.Nat_instMulZeroClass) xs.

Fixpoint svc_list_sum_canonical (xs : seq nat) :
  SubNatRel (foldr addn O xs)
    (svc_target_list_sum (svc_nat_list_to_imported xs)).
Proof.
  destruct xs as [|x tail].
  - exact (sub_nat_rel_canonical O).
  - exact (svc_target_add_related x (sub_nat_to_imported x)
      (foldr addn O tail)
      (svc_target_list_sum (svc_nat_list_to_imported tail))
      (sub_nat_rel_canonical x) (svc_list_sum_canonical tail)).
Defined.

Lemma svc_list_sum_related (xsR : seq nat)
    (xsL : ImportedBusySbf.List_inst1 Lean.Nat) :
  SvcNatListRel xsR xsL ->
  SubNatRel (foldr addn O xsR) (svc_target_list_sum xsL).
Proof.
  intro Hxs. unfold SvcNatListRel in Hxs.
  exact (sub_imported_eq_trans _ _ _ (svc_list_sum_canonical xsR)
    (sub_imported_eq_congr svc_target_list_sum _ _ Hxs)).
Qed.

Definition SvcCoreEnumerationRel (CoreR : finType) (CoreL : Type)
    (toL : CoreR -> CoreL)
    (enumL : ImportedBusySbf.List CoreL) : SProp :=
  Lean.eq (svc_list_to_imported (map toL (enum CoreR))) enumL.

Definition SvcCoreNatFunRel (CoreR : finType) (CoreL : Type)
    (toL : CoreR -> CoreL) (fR : CoreR -> nat)
    (fL : CoreL -> Lean.Nat) : SProp :=
  forall cR, SubNatRel (fR cR) (fL (toL cR)).

Fixpoint svc_map_core_values_canonical
    (CoreR : finType) (CoreL : Type) (toL : CoreR -> CoreL)
    (fR : CoreR -> nat) (fL : CoreL -> Lean.Nat)
    (Hf : SvcCoreNatFunRel CoreR CoreL toL fR fL)
    (xs : seq CoreR) :
  Lean.eq (svc_nat_list_to_imported (map fR xs))
    (ImportedBusySbf.List_map_inst2 CoreL Lean.Nat fL
      (svc_list_to_imported (map toL xs))) :=
  match xs with
  | [::] => @Lean.eq_refl _ _
  | x :: tail => sub_imported_eq_congr2
      (ImportedBusySbf.List_cons_inst1 Lean.Nat) _ _ _ _
      (Hf x)
      (svc_map_core_values_canonical CoreR CoreL toL fR fL Hf tail)
  end.

Lemma svc_map_core_values_related
    (CoreR : finType) (CoreL : Type) (toL : CoreR -> CoreL)
    (fR : CoreR -> nat) (fL : CoreL -> Lean.Nat)
    (enumL : ImportedBusySbf.List CoreL) :
  SvcCoreNatFunRel CoreR CoreL toL fR fL ->
  SvcCoreEnumerationRel CoreR CoreL toL enumL ->
  SvcNatListRel (map fR (enum CoreR))
    (ImportedBusySbf.List_map_inst2 CoreL Lean.Nat fL enumL).
Proof.
  intros Hf Henum. unfold SvcNatListRel, SvcCoreEnumerationRel in *.
  exact (sub_imported_eq_trans _ _ _
    (svc_map_core_values_canonical CoreR CoreL toL fR fL Hf
      (enum CoreR))
    (sub_imported_eq_congr
      (ImportedBusySbf.List_map_inst2 CoreL Lean.Nat fL) _ _ Henum)).
Qed.

Lemma svc_mathcomp_big_seq_as_fold_core (CoreR : Type)
    (xs : seq CoreR) (fR : CoreR -> nat) :
  Logic.eq (\sum_(c <- xs) fR c) (foldr addn O (map fR xs)).
Proof.
  elim: xs => [|x tail IH].
  - rewrite big_nil. reflexivity.
  - rewrite big_cons. cbn [map foldr]. now rewrite IH.
Qed.

Lemma svc_finite_sum_related
    (CoreR : finType) (CoreL : Type) (toL : CoreR -> CoreL)
    (fR : CoreR -> nat) (fL : CoreL -> Lean.Nat)
    (enumL : ImportedBusySbf.List CoreL) :
  SvcCoreNatFunRel CoreR CoreL toL fR fL ->
  SvcCoreEnumerationRel CoreR CoreL toL enumL ->
  SubNatRel (\sum_(c : CoreR) fR c)
    (svc_target_list_sum
      (ImportedBusySbf.List_map_inst2 CoreL Lean.Nat fL enumL)).
Proof.
  intros Hf Henum. rewrite -big_enum.
  rewrite (svc_mathcomp_big_seq_as_fold_core CoreR (enum CoreR) fR).
  apply svc_list_sum_related.
  exact (svc_map_core_values_related CoreR CoreL toL fR fL enumL
    Hf Henum).
Qed.

Inductive SvcSourceTrue : SProp := svc_source_true_intro.
Inductive SvcSourceFalse : SProp := .

Definition SvcSourceBoolTruth (b : bool) : SProp :=
  match b with true => SvcSourceTrue | false => SvcSourceFalse end.

Definition svc_source_false_elim (Q : SProp)
    (H : SvcSourceFalse) : Q := match H return Q with end.

Definition svc_coq_false_ne_true (H : Logic.eq false true) :
    SvcSourceFalse :=
  match H in Logic.eq _ z return
    match z with true => SvcSourceFalse | false => SvcSourceTrue end
  with Logic.eq_refl => svc_source_true_intro end.

Definition svc_prop_to_source_truth (b : bool) :
    is_true b -> SvcSourceBoolTruth b :=
  match b return is_true b -> SvcSourceBoolTruth b with
  | true => fun _ => svc_source_true_intro
  | false => fun H => svc_source_false_elim _ (svc_coq_false_ne_true H)
  end.

Definition svc_bool_true_elim (bR : bool) (bL : ImportedBusySbf.Bool) :
  SvcBoolRel bR bL -> Lean.eq bL ImportedBusySbf.Bool_true ->
  SvcSourceBoolTruth bR.
Proof.
  destruct bR, bL; cbn; intros Hrel Htrue.
  - exact svc_source_true_intro.
  - exact svc_source_true_intro.
  - exact (svc_false_elim _ (svc_false_ne_true Htrue)).
  - exact (svc_false_elim _ (svc_false_ne_true Hrel)).
Defined.

Lemma svc_bool_rel_from_truth (bR : bool) (bL : ImportedBusySbf.Bool) :
  (is_true bR -> Lean.eq bL ImportedBusySbf.Bool_true) ->
  (Lean.eq bL ImportedBusySbf.Bool_true ->
    StrictlyInhabited (is_true bR)) ->
  SvcBoolRel bR bL.
Proof.
  destruct bR, bL; cbn; intros Hforward Hbackward.
  - exact (svc_false_elim _
      (svc_false_ne_true (Hforward (Logic.eq_refl true)))).
  - exact (@Lean.eq_refl _ _).
  - exact (@Lean.eq_refl _ _).
  - destruct (Hbackward (@Lean.eq_refl _ _)) as [Hfalse].
    exact (svc_source_false_elim _ (svc_coq_false_ne_true Hfalse)).
Qed.

Definition svc_exists_intro_strict (T : finType) (p : pred T) (x : T) :
    SvcSourceBoolTruth (p x) ->
    StrictlyInhabited (is_true [exists y : T, p y]).
Proof.
  destruct (p x) eqn:Hpx.
  - intro Htruth. apply strictly_inhabits. apply/existsP. exists x.
    exact Hpx.
  - exact (svc_source_false_elim _).
Defined.

Lemma svc_mathcomp_exists_as_has_enum (T : finType) (p : pred T) :
  [exists x : T, p x] = has p (enum T).
Proof.
  apply/idP/idP.
  - move/existsP=> [x Hx]. apply/hasP. exists x; first exact: mem_enum.
    exact Hx.
  - move/hasP=> [x _ Hx]. apply/existsP. by exists x.
Qed.

Fixpoint svc_exists_forward_seq
    (CoreR CoreL : Type) (toL : CoreR -> CoreL)
    (pR : CoreR -> bool) (pL : CoreL -> ImportedBusySbf.Bool)
    (Hpred : forall cR, SvcBoolRel (pR cR) (pL (toL cR)))
    (xs : seq CoreR) :
  SvcSourceBoolTruth (has pR xs) ->
  ImportedBusySbf.Exists CoreL
    (fun cL => Lean.eq (pL cL) ImportedBusySbf.Bool_true) :=
  match xs as ys return
    SvcSourceBoolTruth (has pR ys) ->
    ImportedBusySbf.Exists CoreL
      (fun cL => Lean.eq (pL cL) ImportedBusySbf.Bool_true)
  with
  | [::] => svc_source_false_elim _
  | cR :: tail =>
      match pR cR as b return
        SvcBoolRel b (pL (toL cR)) ->
        SvcSourceBoolTruth (b || has pR tail) ->
        ImportedBusySbf.Exists CoreL
          (fun cL => Lean.eq (pL cL) ImportedBusySbf.Bool_true)
      with
      | true => fun Hrel _ => ImportedBusySbf.Exists_intro _ _ (toL cR)
          (sub_imported_eq_sym _ _ Hrel)
      | false => fun _ Htail =>
          svc_exists_forward_seq CoreR CoreL toL pR pL Hpred tail Htail
      end (Hpred cR)
  end.

Section ProcessorStateObservations.

  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedBusySbf.Prosa_Behavior_Schedule_ProcessorState Job
      (svc_decidable_eq Job).

  Let StateR : Type := @prosa.behavior.schedule.State Job PStateR.
  Let CoreR : finType := @prosa.behavior.schedule.Core Job PStateR.
  Let StateL : Type :=
    ImportedBusySbf.Prosa_Behavior_Schedule_ProcessorState_State Job
      (svc_decidable_eq Job) PStateL.
  Let CoreL : Type :=
    ImportedBusySbf.Prosa_Behavior_Schedule_ProcessorState_Core Job
      (svc_decidable_eq Job) PStateL.

  Definition svc_target_scheduled_on (j : Job) (s : StateL)
      (c : CoreL) : ImportedBusySbf.Bool :=
    ImportedBusySbf.Prosa_Behavior_Schedule_ProcessorState_scheduled_on
      Job (svc_decidable_eq Job) PStateL j s c.

  Definition svc_target_service_on (j : Job) (s : StateL)
      (c : CoreL) : Lean.Nat :=
    ImportedBusySbf.Prosa_Behavior_Schedule_ProcessorState_service_on
      Job (svc_decidable_eq Job) PStateL j s c.

  Record SvcProcessorStateRel : Type := {
    svc_ps_state_rel : StateR -> StateL -> SProp;
    svc_ps_state_to_target : StateR -> StateL;
    svc_ps_state_to_source : StateL -> StateR;
    svc_ps_core_to_target : CoreR -> CoreL;
    svc_ps_core_to_source : CoreL -> CoreR;
    svc_ps_state_source_roundtrip : forall sR,
      Logic.eq (svc_ps_state_to_source (svc_ps_state_to_target sR)) sR;
    svc_ps_state_target_roundtrip : forall sL,
      Lean.eq (svc_ps_state_to_target (svc_ps_state_to_source sL)) sL;
    svc_ps_core_source_roundtrip : forall cR,
      Logic.eq (svc_ps_core_to_source (svc_ps_core_to_target cR)) cR;
    svc_ps_core_target_roundtrip : forall cL,
      Lean.eq (svc_ps_core_to_target (svc_ps_core_to_source cL)) cL;
    svc_ps_state_rel_canonical : forall sR,
      svc_ps_state_rel sR (svc_ps_state_to_target sR);
    svc_ps_state_rel_surjective : forall sL,
      svc_ps_state_rel (svc_ps_state_to_source sL) sL;
    svc_ps_core_enumeration_rel :
      SvcCoreEnumerationRel CoreR CoreL svc_ps_core_to_target
        (ImportedBusySbf.Prosa_Validation_ScheduleInterface_coreEnumeration
          Job (svc_decidable_eq Job) PStateL);
    svc_ps_scheduled_on_rel :
      forall (j : Job) (sR : StateR) (sL : StateL) (cR : CoreR),
        svc_ps_state_rel sR sL ->
        SvcBoolRel (@prosa.behavior.schedule.scheduled_on Job PStateR
            j sR cR)
          (svc_target_scheduled_on j sL (svc_ps_core_to_target cR));
    svc_ps_service_on_rel :
      forall (j : Job) (sR : StateR) (sL : StateL) (cR : CoreR),
        svc_ps_state_rel sR sL ->
        SubNatRel (@prosa.behavior.schedule.service_on Job PStateR
            j sR cR)
          (svc_target_service_on j sL (svc_ps_core_to_target cR))
  }.

  Variable R : SvcProcessorStateRel.

  Lemma svc_scheduled_on_target_core (j : Job)
      (sR : StateR) (sL : StateL) (cL : CoreL) :
    svc_ps_state_rel R sR sL ->
    SvcBoolRel (@prosa.behavior.schedule.scheduled_on Job PStateR
        j sR (svc_ps_core_to_source R cL))
      (svc_target_scheduled_on j sL cL).
  Proof.
    intro Hstate. unfold SvcBoolRel.
    exact (sub_imported_eq_trans _ _ _
      (svc_ps_scheduled_on_rel R j sR sL
        (svc_ps_core_to_source R cL) Hstate)
      (sub_imported_eq_congr (svc_target_scheduled_on j sL) _ _
        (svc_ps_core_target_roundtrip R cL))).
  Qed.

  Theorem svc_scheduled_in_related (j : Job)
      (sR : StateR) (sL : StateL) :
    svc_ps_state_rel R sR sL ->
    SvcBoolRel (@prosa.behavior.schedule.scheduled_in Job PStateR j sR)
      (ImportedBusySbf.Prosa_Behavior_Schedule_ProcessorState_scheduled_in
        Job (svc_decidable_eq Job) PStateL j sL).
  Proof.
    intro Hstate. apply svc_bool_rel_from_truth.
    - intro Hsource.
      have Htruth := svc_prop_to_source_truth _ Hsource.
      unfold prosa.behavior.schedule.scheduled_in in Htruth.
      rewrite svc_mathcomp_exists_as_has_enum in Htruth.
      apply (ImportedBusySbf.mpr _ _
        (ImportedBusySbf.Prosa_Validation_ScheduleInterface_production_scheduled_in_eq_true_iff
          Job (svc_decidable_eq Job) PStateL j sL)).
      exact (svc_exists_forward_seq CoreR CoreL
        (svc_ps_core_to_target R)
        [eta @prosa.behavior.schedule.scheduled_on Job PStateR j sR]
        (svc_target_scheduled_on j sL)
        (fun cR => svc_ps_scheduled_on_rel R j sR sL cR Hstate)
        (enum CoreR) Htruth).
    - intro Htarget.
      have Hexists := ImportedBusySbf.mp _ _
        (ImportedBusySbf.Prosa_Validation_ScheduleInterface_production_scheduled_in_eq_true_iff
          Job (svc_decidable_eq Job) PStateL j sL) Htarget.
      destruct Hexists as [cL Hscheduled].
      apply (svc_exists_intro_strict CoreR
        [eta @prosa.behavior.schedule.scheduled_on Job PStateR j sR]
        (svc_ps_core_to_source R cL)).
      exact (svc_bool_true_elim _ _
        (svc_scheduled_on_target_core j sR sL cL Hstate) Hscheduled).
  Qed.

  Theorem svc_service_in_related (j : Job)
      (sR : StateR) (sL : StateL) :
    svc_ps_state_rel R sR sL ->
    SubNatRel (@prosa.behavior.schedule.service_in Job PStateR j sR)
      (ImportedBusySbf.Prosa_Behavior_Schedule_ProcessorState_service_in
        Job (svc_decidable_eq Job) PStateL j sL).
  Proof.
    intro Hstate.
    have Hsum := svc_finite_sum_related CoreR CoreL
      (svc_ps_core_to_target R)
      (fun cR => @prosa.behavior.schedule.service_on Job PStateR j sR cR)
      (svc_target_service_on j sL)
      (ImportedBusySbf.Prosa_Validation_ScheduleInterface_coreEnumeration
        Job (svc_decidable_eq Job) PStateL)
      (fun cR => svc_ps_service_on_rel R j sR sL cR Hstate)
      (svc_ps_core_enumeration_rel R).
    unfold SubNatRel in Hsum |- *.
    exact (sub_imported_eq_trans _ _ _ Hsum
      (sub_imported_eq_sym _ _
        (ImportedBusySbf.Prosa_Validation_ScheduleInterface_production_service_in_as_list_sum
          Job (svc_decidable_eq Job) PStateL j sL))).
  Qed.

  Definition SvcScheduleRel
      (schedR : @prosa.behavior.schedule.schedule Job PStateR)
      (schedL : ImportedBusySbf.Prosa_Behavior_Schedule_schedule Job
        (svc_decidable_eq Job) PStateL) : SProp :=
    forall tR tL, SubNatRel tR tL ->
      svc_ps_state_rel R (schedR tR) (schedL tL).

End ProcessorStateObservations.

Goal Logic.True.
Proof. idtac "AUDIT_BEGIN svc_schedule_operations". exact I. Qed.
Print Assumptions svc_finite_sum_related.
Print Assumptions svc_scheduled_in_related.
Print Assumptions svc_service_in_related.
Goal Logic.True.
Proof. idtac "AUDIT_END svc_schedule_operations". exact I. Qed.
