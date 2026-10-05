# `pp_delta`

- Kind (Rocq): Definition
- Rocq: `prosa.results.generality.gel.pp_delta`
- Lean: `Prosa.Results.Generality.Gel.pp_delta`
- Certificate: `pp_delta_correspondence`

## Official Rocq

```coq
pp_delta :
forall {Task : TaskType},
PriorityPoint Task ->
Equality.sort Task -> Equality.sort Task -> GRing.Nmodule.sort ssrint_int__canonical__GRing_Nmodule

pp_delta is not universe polymorphic
Arguments pp_delta {Task H} tsk tsk'
pp_delta is transparent
Expands to: Constant prosa.results.generality.gel.pp_delta
Declared in library prosa.results.generality.gel, line 113, characters 15-23
@pp_delta
     : forall Task : TaskType,
       PriorityPoint Task ->
       Equality.sort Task -> Equality.sort Task -> GRing.Nmodule.sort ssrint_int__canonical__GRing_Nmodule
```

Body:

```coq
pp_delta =
fun (Task : TaskType) (H : PriorityPoint Task) (tsk tsk' : Equality.sort Task) =>
(@task_priority_point Task H tsk' - @task_priority_point Task H tsk)%R
     : forall {Task : TaskType},
       PriorityPoint Task ->
       Equality.sort Task -> Equality.sort Task -> GRing.Nmodule.sort ssrint_int__canonical__GRing_Nmodule

Arguments pp_delta {Task H} tsk tsk'
```

## Lean

```lean
@Prosa.Results.Generality.Gel.pp_delta : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Priority.Gel.PriorityPoint Task] → Task → Task → ℤ
```

Body:

```lean
def Prosa.Results.Generality.Gel.pp_delta.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] → [Prosa.Model.Priority.Gel.PriorityPoint Task] → Task → Task → ℤ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Priority.Gel.PriorityPoint Task] tsk tsk' =>
  Prosa.Model.Priority.Gel.task_priority_point tsk' - Prosa.Model.Priority.Gel.task_priority_point tsk
```

## Lean, imported into Rocq

```coq
Prosa_Results_Generality_Gel_pp_delta
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Priority_Gel_PriorityPoint Task
         inst_3 ->
       Task -> Task -> Int
```

Body:

```coq
Prosa_Results_Generality_Gel_pp_delta@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_10 : Prosa_Model_Priority_Gel_PriorityPoint
                                                                          Task
                                                                          inst_3)
  (tsk tsk' : Task) =>
HSub_hSub_inst7 Prosa_Model_Priority_Gel_offset Prosa_Model_Priority_Gel_offset
  Prosa_Model_Priority_Gel_offset (instHSub_inst1 Prosa_Model_Priority_Gel_offset Int_instSub)
  (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
     inst_3
     inst_10 tsk')
  (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
     inst_3
     inst_10 tsk)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Priority_Gel_PriorityPoint Task
         inst_3 ->
       Task -> Task -> Int

Arguments Prosa_Results_Generality_Gel_pp_delta Task
  inst_3
  inst_10 tsk tsk'
```
