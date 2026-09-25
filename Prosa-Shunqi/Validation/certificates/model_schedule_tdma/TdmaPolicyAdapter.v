From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
From prosa Require Import model.schedule.tdma.
From LeanImport Require Import Lean.
From FoundationImported Require Import ImportedTdmaProjectedFull.
From FoundationCertificates Require Import
  PropSPropFoundation LogicalRelation SubadditivityNatCorrespondence
  TdmaBaseAdapter TdmaSeqsetAdapter.

(** Source `eqType` and the exact compiled Lean class fields. *)
Definition TdmaSlotRel (Task : eqType)
    (slotR : prosa.model.schedule.tdma.TDMA_slot Task)
    (slotL : Task -> Lean.Nat) : SProp :=
  forall tsk : Task, SubNatRel (slotR tsk) (slotL tsk).

Definition TdmaOrderRel (Task : eqType)
    (orderR : prosa.model.schedule.tdma.TDMA_slot_order Task)
    (orderL : Task -> Task -> ImportedTdmaProjectedFull.Bool) : SProp :=
  forall x y : Task, ArBoolRel (orderR x y) (orderL x y).

Record TdmaPolicyRel (Task : eqType)
    (policyR : prosa.model.schedule.tdma.TDMAPolicy Task)
    (policyL : ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_TDMAPolicy
      Task (ar_decidable_eq Task)) : SProp := {
  tdma_slot_related : TdmaSlotRel Task
    (@prosa.model.schedule.tdma.task_time_slot Task policyR)
    (ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_TDMAPolicy_task_time_slot
      Task (ar_decidable_eq Task) policyL);
  tdma_order_related : TdmaOrderRel Task
    (@prosa.model.schedule.tdma.slot_order Task policyR)
    (ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_TDMAPolicy_slot_order
      Task (ar_decidable_eq Task) policyL)
}.

Definition tdma_import_policy (Task : eqType)
    (policyR : prosa.model.schedule.tdma.TDMAPolicy Task) :
    ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_TDMAPolicy
      Task (ar_decidable_eq Task) :=
  ImportedTdmaProjectedFull.Prosa_Model_Schedule_Tdma_TDMAPolicy_mk
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

Print Assumptions tdma_policy_source_total.
