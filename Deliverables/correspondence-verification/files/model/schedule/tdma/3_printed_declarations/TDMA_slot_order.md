# `TDMA_slot_order`

- Kind (Rocq): Definition
- Rocq: `prosa.model.schedule.tdma.TDMA_slot_order`
- Lean: `Prosa.Model.Schedule.Tdma.TDMA_slot_order`
- Certificate: `TDMA_slot_order_source_total, TDMA_slot_order_target_total`

## Official Rocq

```coq
TDMA_slot_order : eqType -> Type

TDMA_slot_order is not universe polymorphic
Arguments TDMA_slot_order Task
TDMA_slot_order is transparent
Expands to: Constant prosa.model.schedule.tdma.TDMA_slot_order
Declared in library prosa.model.schedule.tdma, line 33, characters 13-28
TDMA_slot_order
     : eqType -> Type
```

Body:

```coq
TDMA_slot_order = fun Task : eqType => rel (Equality.sort Task)
     : eqType -> Type

Arguments TDMA_slot_order Task
```

## Lean

```lean
Prosa.Model.Schedule.Tdma.TDMA_slot_order : (Task : Type u_1) → [DecidableEq Task] → Type u_1
def Prosa.Model.Schedule.Tdma.TDMA_slot_order.{u} : (Task : Type u) → [DecidableEq Task] → Type u :=
fun Task [DecidableEq Task] => Task → Task → Bool
```

## Lean, imported into Rocq

```coq
Prosa_Model_Schedule_Tdma_TDMA_slot_order
     : forall Task : Type, DecidableEq Task -> Type
```

Body:

```coq
Prosa_Model_Schedule_Tdma_TDMA_slot_order@{u Lean.u+1.0} =
fun (Task : Type) (_ : DecidableEq Task) => Task -> Task -> Bool
     : forall Task : Type, DecidableEq Task -> Type

Arguments Prosa_Model_Schedule_Tdma_TDMA_slot_order Task%_type_scope
  inst_3
```
