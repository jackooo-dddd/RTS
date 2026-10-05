# `taskT_to_task`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.task.taskT_to_task`
- Lean: `Prosa.Implementation.Refinements.Task.taskT_to_task`
- Certificate: `taskT_to_task_correspondence`

## Official Rocq

```coq
taskT_to_task : @task_T binnat.N -> Equality.sort Task

taskT_to_task is not universe polymorphic
Arguments taskT_to_task tsk
taskT_to_task is transparent
Expands to: Constant prosa.implementation.refinements.task.taskT_to_task
Declared in library prosa.implementation.refinements.task, line 102, characters 11-24
taskT_to_task
     : @task_T binnat.N -> Equality.sort Task
```

Body:

```coq
taskT_to_task =
fun tsk : @task_T binnat.N =>
match tsk with
| {|
    task_id_T := id;
    task_cost_T := cost;
    task_arrival_T := arrival_bound;
    task_deadline_T := deadline;
    task_priority_T := priority
  |} =>
    {|
      task_id := nat_of_bin id;
      task_cost := nat_of_bin cost;
      task_arrival := task_abT_to_task_ab arrival_bound;
      task_deadline := nat_of_bin deadline;
      task_priority := nat_of_bin priority
    |}
end
     : @task_T binnat.N -> Equality.sort Task

Arguments taskT_to_task tsk
```

## Lean

```lean
Prosa.Implementation.Refinements.Task.taskT_to_task : Prosa.Implementation.Refinements.Task.task_T
    Prosa.Implementation.Refinements.Refinements.N →
  Prosa.Implementation.Refinements.Task.Task
```

Body:

```lean
def Prosa.Implementation.Refinements.Task.taskT_to_task : Prosa.Implementation.Refinements.Task.task_T
    Prosa.Implementation.Refinements.Refinements.N →
  Prosa.Implementation.Refinements.Task.Task :=
fun tsk =>
  match tsk with
  |
  { task_id_T := id, task_cost_T := cost, task_arrival_T := arrival_bound, task_deadline_T := deadline,
      task_priority_T := priority } =>
    { task_id := Prosa.Implementation.Refinements.Refinements.nat_of_bin id,
      task_cost := Prosa.Implementation.Refinements.Refinements.nat_of_bin cost,
      task_arrival := Prosa.Implementation.Refinements.ArrivalBound.task_abT_to_task_ab arrival_bound,
      task_deadline := Prosa.Implementation.Refinements.Refinements.nat_of_bin deadline,
      task_priority := Prosa.Implementation.Refinements.Refinements.nat_of_bin priority }
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Task_taskT_to_task
     : Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
       Prosa_Implementation_Refinements_Task_Task
```

Body:

```coq
Prosa_Implementation_Refinements_Task_taskT_to_task@{} =
fun tsk : Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N =>
Prosa_Implementation_Refinements_Task_taskT_to_task_match_1
  (fun _ : Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N =>
   Prosa_Implementation_Refinements_Task_Task)
  tsk
  (fun (id cost : Prosa_Implementation_Refinements_Refinements_N)
     (arrival_bound : Prosa_Implementation_Refinements_ArrivalBound_task_arrivals_bound_T
                        Prosa_Implementation_Refinements_Refinements_N)
     (deadline priority : Prosa_Implementation_Refinements_Refinements_N) =>
   Prosa_Implementation_Definitions_Task_concrete_task_mk
     (Prosa_Implementation_Refinements_Refinements_nat_of_bin id)
     (Prosa_Implementation_Refinements_Refinements_nat_of_bin cost)
     (Prosa_Implementation_Refinements_ArrivalBound_task_abT_to_task_ab arrival_bound)
     (Prosa_Implementation_Refinements_Refinements_nat_of_bin deadline)
     (Prosa_Implementation_Refinements_Refinements_nat_of_bin priority))
     : Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N ->
       Prosa_Implementation_Refinements_Task_Task

Arguments Prosa_Implementation_Refinements_Task_taskT_to_task tsk
```
