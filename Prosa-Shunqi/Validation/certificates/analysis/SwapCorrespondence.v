From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From prosa Require Import analysis.transform.swap.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedSwap ImportedSubadditivity.
From FoundationCertificates Require Import PropSPropFoundation
  LogicalRelation SubadditivityNatCorrespondence SwapNatEquality.

(** The state representation is two-sided.  These maps are logical-relation
    inputs for possibly different Rocq and Lean carrier types, not unproved
    preservation premises for either target operation. *)
Record SwapStateIso (StateR StateL : Type) := {
  swap_toL : StateR -> StateL;
  swap_toR : StateL -> StateR;
  swap_left_roundtrip : forall s, Logic.eq (swap_toR (swap_toL s)) s;
  swap_right_roundtrip : forall s, Logic.eq (swap_toL (swap_toR s)) s
}.

Definition SwapStateRel {StateR StateL : Type}
    (I : SwapStateIso StateR StateL) (sR : StateR) (sL : StateL) : SProp :=
  Lean.eq (swap_toL _ _ I sR) sL.

Section SwapCorrespondence.
  Context (Job : eqType).
  Context (PStateR : prosa.behavior.schedule.ProcessorState Job).
  Variable PStateL :
    ImportedSwap.Prosa_Behavior_Schedule_ProcessorState Job
      (swap_decidable_eq Job).

  Let StateR : Type := @prosa.behavior.schedule.State Job PStateR.
  Let StateL : Type :=
    ImportedSwap.Prosa_Behavior_Schedule_ProcessorState_State Job
      (swap_decidable_eq Job) PStateL.
  Variable I : SwapStateIso StateR StateL.

  Definition SwapScheduleRel
      (schedR : @prosa.behavior.schedule.schedule Job PStateR)
      (schedL : ImportedSwap.Prosa_Behavior_Schedule_schedule Job
        (swap_decidable_eq Job) PStateL) : SProp :=
    forall tR tL, SubNatRel tR tL ->
      SwapStateRel I (schedR tR) (schedL tL).

  Lemma replace_at_correspondence
      (schedR : @prosa.behavior.schedule.schedule Job PStateR)
      (schedL : ImportedSwap.Prosa_Behavior_Schedule_schedule Job
        (swap_decidable_eq Job) PStateL)
      (tR' : nat) (tL' : Lean.Nat)
      (newR : StateR) (newL : StateL) :
    SwapScheduleRel schedR schedL ->
    SubNatRel tR' tL' ->
    SwapStateRel I newR newL ->
    SwapScheduleRel
      (@prosa.analysis.transform.swap.replace_at Job PStateR
        schedR tR' newR)
      (ImportedSwap.Prosa_Analysis_Transform_Swap_replace_at Job
        (swap_decidable_eq Job) PStateL schedL tL' newL).
  Proof.
    intros Hsched Ht' Hnew tR tL Ht.
    unfold prosa.analysis.transform.swap.replace_at.
    unfold ImportedSwap.Prosa_Analysis_Transform_Swap_replace_at.
    have Hbeq := swap_nat_beq_related tR' tR tL' tL Ht' Ht.
    unfold swap_nat_beq in Hbeq.
    unfold SwapStateRel.
    rewrite - (imported_eq_to_coq_eq _ _ Hbeq).
    destruct (tR' == tR) eqn:E; cbn [swap_bool_from_rocq
      ImportedSwap.instDecidableEqBool ImportedSwap.ite].
    - exact Hnew.
    - exact (Hsched tR tL Ht).
  Qed.

  Lemma swapped_correspondence
      (schedR : @prosa.behavior.schedule.schedule Job PStateR)
      (schedL : ImportedSwap.Prosa_Behavior_Schedule_schedule Job
        (swap_decidable_eq Job) PStateL)
      (t1R t2R : nat) (t1L t2L : Lean.Nat) :
    SwapScheduleRel schedR schedL ->
    SubNatRel t1R t1L -> SubNatRel t2R t2L ->
    SwapScheduleRel
      (@prosa.analysis.transform.swap.swapped Job PStateR
        schedR t1R t2R)
      (ImportedSwap.Prosa_Analysis_Transform_Swap_swapped Job
        (swap_decidable_eq Job) PStateL schedL t1L t2L).
  Proof.
    intros Hsched Ht1 Ht2.
    unfold prosa.analysis.transform.swap.swapped.
    cbn [ImportedSwap.Prosa_Analysis_Transform_Swap_swapped].
    apply replace_at_correspondence.
    - apply replace_at_correspondence; try assumption.
      exact (Hsched t2R t2L Ht2).
    - exact Ht2.
    - exact (Hsched t1R t1L Ht1).
  Qed.
End SwapCorrespondence.
