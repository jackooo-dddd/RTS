# `valid_taskset_request_bound_function`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.arrival.request_bound_functions.valid_taskset_request_bound_function`
- Lean: `Prosa.Model.Task.Arrival.RequestBoundFunctions.valid_taskset_request_bound_function`
- Certificate: `valid_taskset_request_bound_function_correspondence`

## Official Rocq

```coq
valid_taskset_request_bound_function :
forall {Task : TaskType}, TaskSet (Equality.sort Task) -> (Equality.sort Task -> duration -> work) -> Prop

valid_taskset_request_bound_function is not universe polymorphic
Arguments valid_taskset_request_bound_function {Task} ts request_bound%function_scope
valid_taskset_request_bound_function is transparent
Expands to: Constant prosa.model.task.arrival.request_bound_functions.valid_taskset_request_bound_function
Declared in library prosa.model.task.arrival.request_bound_functions, line 100, characters 13-49
@valid_taskset_request_bound_function
     : forall Task : TaskType,
       TaskSet (Equality.sort Task) -> (Equality.sort Task -> duration -> work) -> Prop
```

Body:

```coq
valid_taskset_request_bound_function =
fun (Task : TaskType) (ts : TaskSet (Equality.sort Task))
  (request_bound : Equality.sort Task -> duration -> work) =>
forall tsk : Equality.sort Task, is_true (tsk \in ts) -> valid_request_bound_function (request_bound tsk)
     : forall {Task : TaskType},
       TaskSet (Equality.sort Task) -> (Equality.sort Task -> duration -> work) -> Prop

Arguments valid_taskset_request_bound_function {Task} ts request_bound%function_scope
```

## Lean

```lean
@Prosa.Model.Task.Arrival.RequestBoundFunctions.valid_taskset_request_bound_function : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [DecidableEq Task] →
    Prosa.Model.Task.Concept.TaskSet Task → (Task → Prosa.Behavior.Time.duration → Prosa.Behavior.Job.work) → Prop
def Prosa.Model.Task.Arrival.RequestBoundFunctions.valid_taskset_request_bound_function.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [DecidableEq Task] →
    Prosa.Model.Task.Concept.TaskSet Task → (Task → Prosa.Behavior.Time.duration → Prosa.Behavior.Job.work) → Prop :=
fun {Task} [DecidableEq Task] ts request_bound =>
  ∀ (tsk : Task),
    decide (tsk ∈ ts) = true →
      Prosa.Model.Task.Arrival.RequestBoundFunctions.valid_request_bound_function (request_bound tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_RequestBoundFunctions_valid_taskset_request_bound_function
     : forall Task : Prosa_Model_Task_Concept_TaskType,
       DecidableEq Task ->
       Prosa_Model_Task_Concept_TaskSet Task ->
       (Task -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) -> SProp
```

Body:

```coq
Prosa_Model_Task_Arrival_RequestBoundFunctions_valid_taskset_request_bound_function@{u_1 Lean.u_1+1.0
Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (ts : Prosa_Model_Task_Concept_TaskSet Task)
  (request_bound : Task -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) =>
forall tsk : Task,
@eq Bool
  (Decidable_decide
     (Membership_mem Task (Prosa_Model_Task_Concept_TaskSet Task) (List_instMembership Task) ts tsk)
     (List_instDecidableMemOfLawfulBEq Task
        (instBEqOfDecidableEq Task
           inst_3)
        (instLawfulBEq Task
           inst_3)
        tsk ts))
  Bool_true ->
Prosa_Model_Task_Arrival_RequestBoundFunctions_valid_request_bound_function (request_bound tsk)
     : forall Task : Prosa_Model_Task_Concept_TaskType,
       DecidableEq Task ->
       Prosa_Model_Task_Concept_TaskSet Task ->
       (Task -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) -> SProp

Arguments Prosa_Model_Task_Arrival_RequestBoundFunctions_valid_taskset_request_bound_function 
  Task inst_3 
  ts request_bound%_function_scope
```
