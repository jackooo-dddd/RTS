# `task_to_taskT`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.task.task_to_taskT`
- Lean: `Prosa.Implementation.Refinements.Task.task_to_taskT`
- Certificate: `task_to_taskT_correspondence`

## Official Rocq

```coq
task_to_taskT : Equality.sort Task -> @task_T binnat.N

task_to_taskT is not universe polymorphic
Arguments task_to_taskT tsk
task_to_taskT is transparent
Expands to: Constant prosa.implementation.refinements.task.task_to_taskT
Declared in library prosa.implementation.refinements.task, line 122, characters 11-24
task_to_taskT
     : Equality.sort Task -> @task_T binnat.N
```

Body:

```coq
task_to_taskT =
fun tsk : Equality.sort Task =>
match tsk with
| {|
    task_id := id;
    task_cost := cost;
    task_arrival := arrival_bound;
    task_deadline := deadline;
    task_priority := priority
  |} =>
    {|
      task_id_T := bin_of_nat id;
      task_cost_T := bin_of_nat cost;
      task_arrival_T := task_ab_to_task_abT arrival_bound;
      task_deadline_T := bin_of_nat deadline;
      task_priority_T := bin_of_nat priority
    |}
end
     : Equality.sort Task -> @task_T binnat.N

Arguments task_to_taskT tsk
```

## Lean

```lean
Prosa.Implementation.Refinements.Task.task_to_taskT : Prosa.Implementation.Refinements.Task.Task →
  Prosa.Implementation.Refinements.Task.task_T Prosa.Implementation.Refinements.Refinements.N
```

Body:

```lean
def Prosa.Implementation.Refinements.Task.task_to_taskT : Prosa.Implementation.Refinements.Task.Task →
  Prosa.Implementation.Refinements.Task.task_T Prosa.Implementation.Refinements.Refinements.N :=
fun tsk =>
  match tsk with
  |
  { task_id := id, task_cost := cost, task_arrival := arrival_bound, task_deadline := deadline,
      task_priority := priority } =>
    { task_id_T := Prosa.Implementation.Refinements.Refinements.bin_of_nat id,
      task_cost_T := Prosa.Implementation.Refinements.Refinements.bin_of_nat cost,
      task_arrival_T := Prosa.Implementation.Refinements.ArrivalBound.task_ab_to_task_abT arrival_bound,
      task_deadline_T := Prosa.Implementation.Refinements.Refinements.bin_of_nat deadline,
      task_priority_T := Prosa.Implementation.Refinements.Refinements.bin_of_nat priority }
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Task_task_to_taskT
     : Prosa_Implementation_Refinements_Task_Task ->
       Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N
```

Body:

```coq
Prosa_Implementation_Refinements_Task_task_to_taskT@{} =
fun tsk : Prosa_Implementation_Refinements_Task_Task =>
Prosa_Implementation_Refinements_Task_task_to_taskT_match_1
  (fun _ : Prosa_Implementation_Refinements_Task_Task =>
   Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N)
  tsk
  (fun (id cost : Nat) (arrival_bound : Prosa_Implementation_Definitions_ArrivalBound_task_arrivals_bound)
     (deadline : Prosa_Behavior_Time_instant) (priority : Nat) =>
   Prosa_Implementation_Refinements_Task_task_T_mk Prosa_Implementation_Refinements_Refinements_N
     (Prosa_Implementation_Refinements_Refinements_bin_of_nat id)
     (Prosa_Implementation_Refinements_Refinements_bin_of_nat cost)
     (Prosa_Implementation_Refinements_ArrivalBound_task_ab_to_task_abT arrival_bound)
     (Prosa_Implementation_Refinements_Refinements_bin_of_nat deadline)
     (Prosa_Implementation_Refinements_Refinements_bin_of_nat priority))
     : Prosa_Implementation_Refinements_Task_Task ->
       Prosa_Implementation_Refinements_Task_task_T Prosa_Implementation_Refinements_Refinements_N

Arguments Prosa_Implementation_Refinements_Task_task_to_taskT tsk
```
