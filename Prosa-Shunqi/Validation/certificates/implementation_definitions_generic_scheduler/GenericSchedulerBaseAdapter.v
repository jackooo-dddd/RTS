From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From prosa Require Import implementation.definitions.generic_scheduler.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedGenericScheduler ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence.

(** Artifact-local instantiation of the accepted Swap Nat/equality adapter. *)
Definition gs_coq_false_to_target (H : Logic.False) :
    ImportedGenericScheduler.False := match H with end.

Definition gs_decidable_eq (T : eqType) :
    ImportedGenericScheduler.DecidableEq T :=
  fun x y =>
    match @eqP T x y with
    | ReflectT H =>
        ImportedGenericScheduler.Decidable_isTrue (Lean.eq x y)
          (coq_eq_to_imported_eq x y H)
    | ReflectF H =>
        ImportedGenericScheduler.Decidable_isFalse (Lean.eq x y)
          (fun HL => gs_coq_false_to_target
            (H (imported_eq_to_coq_eq x y HL)))
    end.

Definition gs_bool_from_rocq (b : bool) :
    ImportedGenericScheduler.Bool :=
  if b then ImportedGenericScheduler.Bool_true
  else ImportedGenericScheduler.Bool_false.

Definition gs_nat_beq (a b : Lean.Nat) :
    ImportedGenericScheduler.Bool :=
  ImportedGenericScheduler.BEq_beq_inst1 Lean.Nat
    (ImportedGenericScheduler.instBEqOfDecidableEq_inst1 Lean.Nat
      ImportedGenericScheduler.instDecidableEqNat) a b.

Lemma gs_nat_beq_related (aR bR : nat) (aL bL : Lean.Nat) :
  SubNatRel aR aL -> SubNatRel bR bL ->
  Lean.eq (gs_bool_from_rocq (aR == bR)) (gs_nat_beq aL bL).
Proof.
  intros Ha Hb.
  have Hrel := sub_nat_eq_correspondence aR aL bR bL Ha Hb.
  destruct (aR == bR) eqn:E.
  - have Hsource : Logic.eq aR bR by apply/eqP; exact E.
    have Htarget := prop_to_sprop _ _ Hrel Hsource.
    unfold gs_bool_from_rocq, gs_nat_beq.
    change (Lean.eq ImportedGenericScheduler.Bool_true
      (ImportedGenericScheduler.Decidable_decide (Lean.eq aL bL)
        (ImportedGenericScheduler.Nat_decEq aL bL))).
    destruct (ImportedGenericScheduler.Nat_decEq aL bL)
      as [Hfalse|Htrue].
    + destruct (Hfalse Htarget).
    + exact (@Lean.eq_refl ImportedGenericScheduler.Bool
        ImportedGenericScheduler.Bool_true).
  - have Hneq : Logic.eq aR bR -> Logic.False.
    { intro H; subst bR. rewrite eqxx in E. discriminate. }
    unfold gs_bool_from_rocq, gs_nat_beq.
    change (Lean.eq ImportedGenericScheduler.Bool_false
      (ImportedGenericScheduler.Decidable_decide (Lean.eq aL bL)
        (ImportedGenericScheduler.Nat_decEq aL bL))).
    destruct (ImportedGenericScheduler.Nat_decEq aL bL)
      as [Hfalse|Htrue].
    + exact (@Lean.eq_refl ImportedGenericScheduler.Bool
        ImportedGenericScheduler.Bool_false).
    + exfalso. exact (Hneq (sprop_to_prop _ _ Hrel Htrue)).
Qed.

Record GsStateIso (StateR StateL : Type) := {
  gs_toL : StateR -> StateL;
  gs_toR : StateL -> StateR;
  gs_left_roundtrip : forall s, Logic.eq (gs_toR (gs_toL s)) s;
  gs_right_roundtrip : forall s, Logic.eq (gs_toL (gs_toR s)) s
}.

Definition GsStateRel {StateR StateL : Type}
    (I : GsStateIso StateR StateL) (sR : StateR) (sL : StateL) : SProp :=
  Lean.eq (gs_toL _ _ I sR) sL.

Lemma gs_state_left_coverage {StateR StateL : Type}
    (I : GsStateIso StateR StateL) (sR : StateR) :
  GsStateRel I sR (gs_toL _ _ I sR).
Proof. exact (@Lean.eq_refl _ _). Qed.

Lemma gs_state_right_coverage {StateR StateL : Type}
    (I : GsStateIso StateR StateL) (sL : StateL) :
  GsStateRel I (gs_toR _ _ I sL) sL.
Proof.
  unfold GsStateRel.
  exact (coq_eq_to_imported_eq _ _ (gs_right_roundtrip _ _ I sL)).
Qed.

Section GenericSchedulerRelation.
  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedGenericScheduler.Prosa_Behavior_Schedule_ProcessorState Job
      (gs_decidable_eq Job).

  Let StateR : Type := @prosa.behavior.schedule.State Job PStateR.
  Let StateL : Type :=
    ImportedGenericScheduler.Prosa_Behavior_Schedule_ProcessorState_State
      Job (gs_decidable_eq Job) PStateL.
  Variable I : GsStateIso StateR StateL.

  Definition GsScheduleRel
      (schedR : @prosa.behavior.schedule.schedule Job PStateR)
      (schedL : ImportedGenericScheduler.Prosa_Behavior_Schedule_schedule
        Job (gs_decidable_eq Job) PStateL) : SProp :=
    forall tR tL, SubNatRel tR tL ->
      GsStateRel I (schedR tR) (schedL tL).

  Definition GsPolicyRel
      (policyR : @prosa.implementation.definitions.generic_scheduler.PointwisePolicy
        Job PStateR)
      (policyL :
        ImportedGenericScheduler.Prosa_Implementation_Definitions_GenericScheduler_PointwisePolicy
          Job (gs_decidable_eq Job) PStateL) : SProp :=
    forall schedR schedL,
      GsScheduleRel schedR schedL ->
      forall tR tL, SubNatRel tR tL ->
        GsStateRel I (policyR schedR tR) (policyL schedL tL).

  Lemma gs_constant_policy_coverage (idleR : StateR) (idleL : StateL) :
    GsStateRel I idleR idleL ->
    GsPolicyRel
      (fun _ _ => idleR)
      (fun _ _ => idleL).
  Proof.
    intros Hidle schedR schedL Hsched tR tL Ht.
    exact Hidle.
  Qed.

End GenericSchedulerRelation.
