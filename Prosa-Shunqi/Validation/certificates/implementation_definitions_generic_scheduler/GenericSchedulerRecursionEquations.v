From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedGenericScheduler ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence
  GenericSchedulerBaseAdapter GenericSchedulerOperations.

(** Kernel equations for the actual imported `Nat_brecOn` body.  These are
    deliberately proved against the imported definition, not postulated as
    a statement-only interface. *)
Section GenericSchedulerRecursionEquations.
  Context (Job : eqType).
  Variable PStateL :
    ImportedGenericScheduler.Prosa_Behavior_Schedule_ProcessorState Job
      (gs_decidable_eq Job).
  Let StateL : Type :=
    ImportedGenericScheduler.Prosa_Behavior_Schedule_ProcessorState_State
      Job (gs_decidable_eq Job) PStateL.
  Let PolicyL : Type :=
    ImportedGenericScheduler.Prosa_Implementation_Definitions_GenericScheduler_PointwisePolicy
      Job (gs_decidable_eq Job) PStateL.

  Lemma gs_target_prefix_zero (policyL : PolicyL) (idleL : StateL) :
    Lean.eq
      (ImportedGenericScheduler.Prosa_Implementation_Definitions_GenericScheduler_schedule_up_to
        Job (gs_decidable_eq Job) PStateL policyL idleL Lean.Nat_zero)
      (ImportedGenericScheduler.Prosa_Analysis_Transform_Swap_replace_at
        Job (gs_decidable_eq Job) PStateL
        (ImportedGenericScheduler.Prosa_Implementation_Definitions_GenericScheduler_empty_schedule
          Job (gs_decidable_eq Job) PStateL idleL)
        Lean.Nat_zero
        (policyL
          (ImportedGenericScheduler.Prosa_Implementation_Definitions_GenericScheduler_empty_schedule
            Job (gs_decidable_eq Job) PStateL idleL)
          Lean.Nat_zero)).
  Proof. exact (@Lean.eq_refl _ _). Qed.

  Lemma gs_target_prefix_succ (policyL : PolicyL) (idleL : StateL)
      (h : Lean.Nat) :
    Lean.eq
      (ImportedGenericScheduler.Prosa_Implementation_Definitions_GenericScheduler_schedule_up_to
        Job (gs_decidable_eq Job) PStateL policyL idleL (Lean.Nat_succ h))
      (ImportedGenericScheduler.Prosa_Analysis_Transform_Swap_replace_at
        Job (gs_decidable_eq Job) PStateL
        (ImportedGenericScheduler.Prosa_Implementation_Definitions_GenericScheduler_schedule_up_to
          Job (gs_decidable_eq Job) PStateL policyL idleL h)
        (Lean.Nat_succ h)
        (policyL
          (ImportedGenericScheduler.Prosa_Implementation_Definitions_GenericScheduler_schedule_up_to
            Job (gs_decidable_eq Job) PStateL policyL idleL h)
          (Lean.Nat_succ h))).
  Proof. exact (@Lean.eq_refl _ _). Qed.
End GenericSchedulerRecursionEquations.
