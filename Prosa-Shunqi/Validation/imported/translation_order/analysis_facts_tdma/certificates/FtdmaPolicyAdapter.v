(* Re-bound copy of the accepted certificates/model_schedule_tdma/TdmaPolicyAdapter.v:
   only the imported module (ImportedTdmaProjectedFull -> ImportedFactsTdma)
   and certificate module names (TdmaX -> FtdmaX) are renamed. *)
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import model.schedule.tdma.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedFactsTdma.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  FtdmaBaseAdapter FtdmaSeqsetAdapter.

(** Source `eqType` and the exact compiled Lean class fields. *)
Definition TdmaSlotRel (Task : eqType)
    (slotR : prosa.model.schedule.tdma.TDMA_slot Task)
    (slotL : Task -> Lean.Nat) : SProp :=
  forall tsk : Task, SubNatRel (slotR tsk) (slotL tsk).

Definition TdmaOrderRel (Task : eqType)
    (orderR : prosa.model.schedule.tdma.TDMA_slot_order Task)
    (orderL : Task -> Task -> ImportedFactsTdma.Bool) : SProp :=
  forall x y : Task, ArBoolRel (orderR x y) (orderL x y).

Record TdmaPolicyRel (Task : eqType)
    (policyR : prosa.model.schedule.tdma.TDMAPolicy Task)
    (policyL : ImportedFactsTdma.Prosa_Model_Schedule_Tdma_TDMAPolicy
      Task (ar_decidable_eq Task)) : SProp := {
  tdma_slot_related : TdmaSlotRel Task
    (@prosa.model.schedule.tdma.task_time_slot Task policyR)
    (ImportedFactsTdma.Prosa_Model_Schedule_Tdma_TDMAPolicy_task_time_slot
      Task (ar_decidable_eq Task) policyL);
  tdma_order_related : TdmaOrderRel Task
    (@prosa.model.schedule.tdma.slot_order Task policyR)
    (ImportedFactsTdma.Prosa_Model_Schedule_Tdma_TDMAPolicy_slot_order
      Task (ar_decidable_eq Task) policyL)
}.

Definition tdma_import_policy (Task : eqType)
    (policyR : prosa.model.schedule.tdma.TDMAPolicy Task) :
    ImportedFactsTdma.Prosa_Model_Schedule_Tdma_TDMAPolicy
      Task (ar_decidable_eq Task) :=
  ImportedFactsTdma.Prosa_Model_Schedule_Tdma_TDMAPolicy_mk
    Task (ar_decidable_eq Task)
    (fun tsk => sub_nat_to_imported
      (@prosa.model.schedule.tdma.task_time_slot Task policyR tsk))
    (fun x y => ar_bool_to_imported
      (@prosa.model.schedule.tdma.slot_order Task policyR x y)).

Lemma tdma_policy_source_total (Task : eqType)
    (policyR : prosa.model.schedule.tdma.TDMAPolicy Task) :
  TdmaPolicyRel Task policyR (tdma_import_policy Task policyR).
Proof.
  constructor.
  - intro tsk. exact (sub_nat_rel_canonical _).
  - intros x y. exact (@Lean.eq_refl _ _).
Qed.

(** Carrier coverage for the two representation aliases: every source value
    has a related imported value and vice versa. *)
Definition tdma_import_slot (Task : eqType)
    (slotR : prosa.model.schedule.tdma.TDMA_slot Task) :
    ImportedFactsTdma.Prosa_Model_Schedule_Tdma_TDMA_slot
      Task (ar_decidable_eq Task) :=
  fun tsk => sub_nat_to_imported (slotR tsk).

Definition tdma_export_slot (Task : eqType)
    (slotL : ImportedFactsTdma.Prosa_Model_Schedule_Tdma_TDMA_slot
      Task (ar_decidable_eq Task)) :
    prosa.model.schedule.tdma.TDMA_slot Task :=
  fun tsk => sub_nat_to_rocq (slotL tsk).

Lemma TDMA_slot_source_total (Task : eqType)
    (slotR : prosa.model.schedule.tdma.TDMA_slot Task) :
  TdmaSlotRel Task slotR (tdma_import_slot Task slotR).
Proof. intro tsk. exact (sub_nat_rel_canonical _). Qed.

Lemma TDMA_slot_target_total (Task : eqType)
    (slotL : ImportedFactsTdma.Prosa_Model_Schedule_Tdma_TDMA_slot
      Task (ar_decidable_eq Task)) :
  TdmaSlotRel Task (tdma_export_slot Task slotL) slotL.
Proof. intro tsk. exact (sub_nat_rel_surjective _). Qed.

Definition tdma_import_slot_order (Task : eqType)
    (orderR : prosa.model.schedule.tdma.TDMA_slot_order Task) :
    ImportedFactsTdma.Prosa_Model_Schedule_Tdma_TDMA_slot_order
      Task (ar_decidable_eq Task) :=
  fun x y => ar_bool_to_imported (orderR x y).

Definition tdma_export_slot_order (Task : eqType)
    (orderL : ImportedFactsTdma.Prosa_Model_Schedule_Tdma_TDMA_slot_order
      Task (ar_decidable_eq Task)) :
    prosa.model.schedule.tdma.TDMA_slot_order Task :=
  fun x y => ar_bool_to_rocq (orderL x y).

Lemma TDMA_slot_order_source_total (Task : eqType)
    (orderR : prosa.model.schedule.tdma.TDMA_slot_order Task) :
  TdmaOrderRel Task orderR (tdma_import_slot_order Task orderR).
Proof. intros x y. exact (@Lean.eq_refl _ _). Qed.

Lemma TDMA_slot_order_target_total (Task : eqType)
    (orderL : ImportedFactsTdma.Prosa_Model_Schedule_Tdma_TDMA_slot_order
      Task (ar_decidable_eq Task)) :
  TdmaOrderRel Task (tdma_export_slot_order Task orderL) orderL.
Proof. intros x y. exact (ar_bool_target_roundtrip _). Qed.

Definition tdma_export_policy (Task : eqType)
    (policyL : ImportedFactsTdma.Prosa_Model_Schedule_Tdma_TDMAPolicy
      Task (ar_decidable_eq Task)) :
    prosa.model.schedule.tdma.TDMAPolicy Task :=
  @prosa.model.schedule.tdma.Build_TDMAPolicy Task
    (tdma_export_slot Task
      (ImportedFactsTdma.Prosa_Model_Schedule_Tdma_TDMAPolicy_task_time_slot
        Task (ar_decidable_eq Task) policyL))
    (tdma_export_slot_order Task
      (ImportedFactsTdma.Prosa_Model_Schedule_Tdma_TDMAPolicy_slot_order
        Task (ar_decidable_eq Task) policyL)).

Lemma tdma_policy_target_total (Task : eqType)
    (policyL : ImportedFactsTdma.Prosa_Model_Schedule_Tdma_TDMAPolicy
      Task (ar_decidable_eq Task)) :
  TdmaPolicyRel Task (tdma_export_policy Task policyL) policyL.
Proof.
  constructor.
  - exact (TDMA_slot_target_total Task _).
  - exact (TDMA_slot_order_target_total Task _).
Qed.

Print Assumptions tdma_policy_source_total.
Print Assumptions tdma_policy_target_total.
