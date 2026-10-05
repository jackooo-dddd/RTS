From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From prosa Require Import implementation.definitions.generic_scheduler.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedGenericScheduler ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence
  GenericSchedulerBaseAdapter GenericSchedulerOperations
  GenericSchedulerRecursionEquations.

Section GenericSchedulerCorrespondence.
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

  Variable policyR :
    @prosa.implementation.definitions.generic_scheduler.PointwisePolicy
      Job PStateR.
  Variable policyL :
    ImportedGenericScheduler.Prosa_Implementation_Definitions_GenericScheduler_PointwisePolicy
      Job (gs_decidable_eq Job) PStateL.
  Hypothesis Hpolicy :
    GsPolicyRel Job PStateR PStateL I policyR policyL.
  Variable idleR : StateR.
  Variable idleL : StateL.
  Hypothesis Hidle : GsStateRel I idleR idleL.

  (** The public pointwise-policy definition unfolds to exactly the
      schedule-prefix/time-to-state function space on both sides.  This
      elimination rule is the typed logical relation for related policies. *)
  Lemma gs_pointwise_policy_application
      (schedR : @prosa.behavior.schedule.schedule Job PStateR)
      (schedL : ImportedGenericScheduler.Prosa_Behavior_Schedule_schedule
        Job (gs_decidable_eq Job) PStateL)
      (tR : nat) (tL : Lean.Nat) :
    GsScheduleRel Job PStateR PStateL I schedR schedL ->
    SubNatRel tR tL ->
    GsStateRel I (policyR schedR tR) (policyL schedL tL).
  Proof.
    intros Hsched Ht.
    exact (Hpolicy schedR schedL Hsched tR tL Ht).
  Qed.

  Lemma gs_prefix_canonical (hR : nat) :
    GsScheduleRel Job PStateR PStateL I
      (@prosa.implementation.definitions.generic_scheduler.schedule_up_to
        Job PStateR policyR idleR hR)
      (ImportedGenericScheduler.Prosa_Implementation_Definitions_GenericScheduler_schedule_up_to
        Job (gs_decidable_eq Job) PStateL policyL idleL
        (sub_nat_to_imported hR)).
  Proof.
    induction hR as [|hR IH].
    - cbn [prosa.implementation.definitions.generic_scheduler.schedule_up_to
        sub_nat_to_imported].
      rewrite (imported_eq_to_coq_eq _ _
        (gs_target_prefix_zero Job PStateL policyL idleL)).
      eapply gs_replace_at_correspondence.
      + exact (gs_empty_schedule_correspondence Job PStateR PStateL I
          idleR idleL Hidle).
      + exact (sub_nat_rel_canonical 0).
      + exact (gs_pointwise_policy_application _ _ _ _
          (gs_empty_schedule_correspondence Job PStateR PStateL I
            idleR idleL Hidle)
          (sub_nat_rel_canonical 0)).
    - cbn [prosa.implementation.definitions.generic_scheduler.schedule_up_to
        sub_nat_to_imported].
      rewrite (imported_eq_to_coq_eq _ _
        (gs_target_prefix_succ Job PStateL policyL idleL
          (sub_nat_to_imported hR))).
      eapply gs_replace_at_correspondence.
      + exact IH.
      + exact (sub_nat_rel_canonical hR.+1).
      + exact (gs_pointwise_policy_application _ _ _ _ IH
          (sub_nat_rel_canonical hR.+1)).
  Qed.

  Lemma gs_prefix_correspondence (hR : nat) (hL : Lean.Nat) :
    SubNatRel hR hL ->
    GsScheduleRel Job PStateR PStateL I
      (@prosa.implementation.definitions.generic_scheduler.schedule_up_to
        Job PStateR policyR idleR hR)
      (ImportedGenericScheduler.Prosa_Implementation_Definitions_GenericScheduler_schedule_up_to
        Job (gs_decidable_eq Job) PStateL policyL idleL hL).
  Proof.
    intro Hh.
    unfold SubNatRel in Hh.
    rewrite <- (imported_eq_to_coq_eq _ _ Hh).
    exact (gs_prefix_canonical hR).
  Qed.

  Lemma gs_generic_schedule_correspondence (tR : nat) (tL : Lean.Nat) :
    SubNatRel tR tL ->
    GsStateRel I
      (@prosa.implementation.definitions.generic_scheduler.generic_schedule
        Job PStateR policyR idleR tR)
      (ImportedGenericScheduler.Prosa_Implementation_Definitions_GenericScheduler_generic_schedule
        Job (gs_decidable_eq Job) PStateL policyL idleL tL).
  Proof.
    intro Ht.
    cbn [prosa.implementation.definitions.generic_scheduler.generic_schedule
      ImportedGenericScheduler.Prosa_Implementation_Definitions_GenericScheduler_generic_schedule].
    exact (gs_prefix_correspondence tR tL Ht tR tL Ht).
  Qed.
End GenericSchedulerCorrespondence.
