From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From prosa Require Import implementation.definitions.generic_scheduler.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedGenericScheduler ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence
  GenericSchedulerBaseAdapter.

Section GenericSchedulerOperations.
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

  Lemma gs_empty_schedule_correspondence
      (idleR : StateR) (idleL : StateL) :
    GsStateRel I idleR idleL ->
    GsScheduleRel Job PStateR PStateL I
      (@prosa.implementation.definitions.generic_scheduler.empty_schedule
        Job PStateR idleR)
      (ImportedGenericScheduler.Prosa_Implementation_Definitions_GenericScheduler_empty_schedule
        Job (gs_decidable_eq Job) PStateL idleL).
  Proof.
    intros Hidle tR tL Ht.
    cbn [prosa.implementation.definitions.generic_scheduler.empty_schedule
      ImportedGenericScheduler.Prosa_Implementation_Definitions_GenericScheduler_empty_schedule].
    exact Hidle.
  Qed.

  Lemma gs_replace_at_correspondence
      (schedR : @prosa.behavior.schedule.schedule Job PStateR)
      (schedL : ImportedGenericScheduler.Prosa_Behavior_Schedule_schedule
        Job (gs_decidable_eq Job) PStateL)
      (tR' : nat) (tL' : Lean.Nat)
      (newR : StateR) (newL : StateL) :
    GsScheduleRel Job PStateR PStateL I schedR schedL ->
    SubNatRel tR' tL' ->
    GsStateRel I newR newL ->
    GsScheduleRel Job PStateR PStateL I
      (@prosa.analysis.transform.swap.replace_at Job PStateR
        schedR tR' newR)
      (ImportedGenericScheduler.Prosa_Analysis_Transform_Swap_replace_at
        Job (gs_decidable_eq Job) PStateL schedL tL' newL).
  Proof.
    intros Hsched Ht' Hnew tR tL Ht.
    unfold prosa.analysis.transform.swap.replace_at.
    unfold ImportedGenericScheduler.Prosa_Analysis_Transform_Swap_replace_at.
    have Hbeq := gs_nat_beq_related tR' tR tL' tL Ht' Ht.
    unfold gs_nat_beq in Hbeq.
    unfold GsStateRel.
    rewrite - (imported_eq_to_coq_eq _ _ Hbeq).
    destruct (tR' == tR) eqn:E; cbn [gs_bool_from_rocq
      ImportedGenericScheduler.instDecidableEqBool
      ImportedGenericScheduler.ite].
    - exact Hnew.
    - exact (Hsched tR tL Ht).
  Qed.
End GenericSchedulerOperations.
