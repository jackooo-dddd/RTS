# `respects_max_request_bound`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.arrival.request_bound_functions.respects_max_request_bound`
- Lean: `Prosa.Model.Task.Arrival.RequestBoundFunctions.respects_max_request_bound`
- Certificate: `respects_max_request_bound_correspondence`

## Official Rocq

```coq
respects_max_request_bound :
forall {Task : TaskType} {Job : JobType},
JobTask Job Task -> JobCost Job -> arrival_sequence Job -> Equality.sort Task -> (duration -> work) -> Prop

respects_max_request_bound is not universe polymorphic
Arguments respects_max_request_bound {Task Job H H0} arr_seq tsk max_request_bound%function_scope
respects_max_request_bound is transparent
Expands to: Constant prosa.model.task.arrival.request_bound_functions.respects_max_request_bound
Declared in library prosa.model.task.arrival.request_bound_functions, line 60, characters 13-39
@respects_max_request_bound
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task ->
       JobCost Job -> arrival_sequence Job -> Equality.sort Task -> (duration -> work) -> Prop
```

Body:

```coq
respects_max_request_bound =
fun (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (H0 : JobCost Job)
  (arr_seq : arrival_sequence Job) (tsk : Equality.sort Task) (max_request_bound : duration -> work) =>
forall t1 t2 : instant,
is_true (t1 <= t2) ->
is_true (@cost_of_task_arrivals Job Task H H0 arr_seq tsk t1 t2 <= max_request_bound (t2 - t1))
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task ->
       JobCost Job -> arrival_sequence Job -> Equality.sort Task -> (duration -> work) -> Prop

Arguments respects_max_request_bound {Task Job H H0} arr_seq tsk max_request_bound%function_scope
```

## Lean

```lean
@Prosa.Model.Task.Arrival.RequestBoundFunctions.respects_max_request_bound : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobCost Job] →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Task → (Prosa.Behavior.Time.duration → Prosa.Behavior.Job.work) → Prop
def Prosa.Model.Task.Arrival.RequestBoundFunctions.respects_max_request_bound.{u_1, u_2} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobCost Job] →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Task → (Prosa.Behavior.Time.duration → Prosa.Behavior.Job.work) → Prop :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task]
    [Prosa.Behavior.Job.JobCost Job] arr_seq tsk max_request_bound =>
  ∀ (t1 t2 : Prosa.Behavior.Time.instant),
    t1 ≤ t2 → Prosa.Model.Task.Arrivals.cost_of_task_arrivals arr_seq tsk t1 t2 ≤ max_request_bound (t2 - t1)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_RequestBoundFunctions_respects_max_request_bound
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_7 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Task -> (Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) -> SProp
```

Body:

```coq
Prosa_Model_Task_Arrival_RequestBoundFunctions_respects_max_request_bound@{u_1 u_2 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_7 : DecidableEq Job)
  (inst_10 : 
   Prosa_Model_Task_Concept_JobTask Job
     inst_7 Task
     inst_3)
  (inst_14 : 
   Prosa_Behavior_Job_JobCost Job
     inst_7)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_7)
  (tsk : Task) (max_request_bound : Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) =>
forall t1 t2 : Prosa_Behavior_Time_instant,
LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t2 ->
LE_le_inst1 Nat instLENat
  (Prosa_Model_Task_Arrivals_cost_of_task_arrivals Job
     inst_7 Task
     inst_3
     inst_10
     inst_14 arr_seq tsk t1 t2)
  (max_request_bound
     (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
        (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t2 t1))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_7 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Task -> (Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) -> SProp

Arguments Prosa_Model_Task_Arrival_RequestBoundFunctions_respects_max_request_bound 
  Task inst_3 
  Job inst_7
  inst_10
  inst_14 
  arr_seq tsk request_bound%_function_scope
```
