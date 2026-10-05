# `TDMA_slot`

- Kind (Rocq): Definition
- Rocq: `prosa.model.schedule.tdma.TDMA_slot`
- Lean: `Prosa.Model.Schedule.Tdma.TDMA_slot`
- Certificate: `TDMA_slot_source_total, TDMA_slot_target_total`

## Official Rocq

```coq
TDMA_slot : eqType -> Type

TDMA_slot is not universe polymorphic
Arguments TDMA_slot Task
TDMA_slot is transparent
Expands to: Constant prosa.model.schedule.tdma.TDMA_slot
Declared in library prosa.model.schedule.tdma, line 28, characters 13-22
TDMA_slot
     : eqType -> Type
```

Body:

```coq
TDMA_slot = fun Task : eqType => Equality.sort Task -> duration
     : eqType -> Type

Arguments TDMA_slot Task
```

## Lean

```lean
Prosa.Model.Schedule.Tdma.TDMA_slot : (Task : Type u_1) → [DecidableEq Task] → Type u_1
def Prosa.Model.Schedule.Tdma.TDMA_slot.{u} : (Task : Type u) → [DecidableEq Task] → Type u :=
fun Task [DecidableEq Task] => Task → Prosa.Behavior.Time.duration
```

## Lean, imported into Rocq

```coq
Prosa_Model_Schedule_Tdma_TDMA_slot
     : forall Task : Type, DecidableEq Task -> Type
```

Body:

```coq
Prosa_Model_Schedule_Tdma_TDMA_slot@{u Lean.u+1.0} =
fun (Task : Type) (_ : DecidableEq Task) => Task -> Prosa_Behavior_Time_duration
     : forall Task : Type, DecidableEq Task -> Type

Arguments Prosa_Model_Schedule_Tdma_TDMA_slot Task%_type_scope
  inst_3
```
