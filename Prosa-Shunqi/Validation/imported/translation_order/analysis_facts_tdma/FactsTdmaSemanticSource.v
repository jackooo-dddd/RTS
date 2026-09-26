Require Export prosa.model.schedule.tdma.
Require Import prosa.util.all.
Require Import prosa.util.notation.

Module FactsTdmaSemanticSource.

Section SourceContext_0.
  Context {Task : eqType}.
  Variable ts : {set Task}.
  Context `{TDMAPolicy Task}.
    Variable task : Task.
    Hypothesis H_task_in_ts : task \in ts.
    Hypothesis time_slot_positive :
      valid_time_slot ts.

Definition statement_TDMA_cycle_ge_each_time_slot : Prop :=
  (forall (Task : eqType) (ts : {set Task}) (H : TDMAPolicy Task) (task : Task), task \in ts -> task_time_slot task <= TDMA_cycle ts).

End SourceContext_0.

Section SourceContext_1.
  Context {Task : eqType}.
  Variable ts : {set Task}.
  Context `{TDMAPolicy Task}.
    Variable task : Task.
    Hypothesis H_task_in_ts : task \in ts.
    Hypothesis time_slot_positive :
      valid_time_slot ts.

Definition statement_TDMA_cycle_positive : Prop :=
  (forall (Task : eqType) (ts : {set Task}) (H : TDMAPolicy Task) (task : Task), task \in ts -> valid_time_slot ts -> 0 < TDMA_cycle ts).

End SourceContext_1.

Section SourceContext_2.
  Context {Task : eqType}.
  Variable ts : {set Task}.
  Context `{TDMAPolicy Task}.
    Variable task : Task.
    Hypothesis H_task_in_ts : task \in ts.
    Hypothesis time_slot_positive :
      valid_time_slot ts.

Definition statement_Offset_lt_cycle : Prop :=
  (forall (Task : eqType) (ts : {set Task}) (H : TDMAPolicy Task) (task : Task), task \in ts -> valid_time_slot ts -> task_slot_offset ts task < TDMA_cycle ts).

End SourceContext_2.

Section SourceContext_3.
  Context {Task : eqType}.
  Variable ts : {set Task}.
  Context `{TDMAPolicy Task}.
    Variable task : Task.
    Hypothesis H_task_in_ts : task \in ts.
    Hypothesis time_slot_positive :
      valid_time_slot ts.

Definition statement_Offset_add_slot_leq_cycle : Prop :=
  (forall (Task : eqType) (ts : {set Task}) (H : TDMAPolicy Task) (task : Task), task \in ts -> task_slot_offset ts task + task_time_slot task <= TDMA_cycle ts).

End SourceContext_3.

Section SourceContext_4.
  Context {Task : eqType}.
  Variable ts : {set Task}.
  Context `{TDMAPolicy Task}.
    Variable task : Task.
    Hypothesis H_task_in_ts : task \in ts.
    Hypothesis time_slot_positive :
      valid_time_slot ts.
    Hypothesis slot_order_total :
      total_slot_order ts.
    Hypothesis slot_order_antisymmetric :
      antisymmetric_slot_order ts.
    Hypothesis slot_order_transitive :
      transitive_slot_order.

Definition statement_relation_offset : Prop :=
  (forall (Task : eqType) (ts : {set Task}) (H : TDMAPolicy Task), antisymmetric_slot_order ts -> transitive_slot_order -> forall tsk1 tsk2 : Task, tsk1 \in ts -> tsk2 \in ts -> slot_order tsk1 tsk2 -> tsk1 != tsk2 -> task_slot_offset ts tsk1 + task_time_slot tsk1 <= task_slot_offset ts tsk2).

End SourceContext_4.

Section SourceContext_5.
  Context {Task : eqType}.
  Variable ts : {set Task}.
  Context `{TDMAPolicy Task}.
    Variable task : Task.
    Hypothesis H_task_in_ts : task \in ts.
    Hypothesis time_slot_positive :
      valid_time_slot ts.
    Hypothesis slot_order_total :
      total_slot_order ts.
    Hypothesis slot_order_antisymmetric :
      antisymmetric_slot_order ts.
    Hypothesis slot_order_transitive :
      transitive_slot_order.

Definition statement_task_in_time_slot_uniq : Prop :=
  (forall (Task : eqType) (ts : {set Task}) (H : TDMAPolicy Task) (task : Task), task \in ts -> valid_time_slot ts -> total_slot_order ts -> antisymmetric_slot_order ts -> transitive_slot_order -> forall (tsk1 tsk2 : Task) (t : instant), tsk1 \in ts -> 0 < task_time_slot tsk1 -> tsk2 \in ts -> 0 < task_time_slot tsk2 -> task_in_time_slot ts tsk1 t -> task_in_time_slot ts tsk2 t -> tsk1 = tsk2).

End SourceContext_5.

End FactsTdmaSemanticSource.
