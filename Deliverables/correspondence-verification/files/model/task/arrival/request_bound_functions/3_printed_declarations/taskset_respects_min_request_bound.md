# `taskset_respects_min_request_bound`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.arrival.request_bound_functions.taskset_respects_min_request_bound`
- Lean: `Prosa.Model.Task.Arrival.RequestBoundFunctions.taskset_respects_min_request_bound`
- Certificate: `taskset_respects_min_request_bound_correspondence`

## Official Rocq

```coq
taskset_respects_min_request_bound :
forall {Task : TaskType} {Job : JobType},
JobTask Job Task ->
JobCost Job -> arrival_sequence Job -> MinRequestBound Task -> TaskSet (Equality.sort Task) -> Prop

taskset_respects_min_request_bound is not universe polymorphic
Arguments taskset_respects_min_request_bound {Task Job H H0} arr_seq {H2} ts
taskset_respects_min_request_bound is transparent
Expands to: Constant prosa.model.task.arrival.request_bound_functions.taskset_respects_min_request_bound
Declared in library prosa.model.task.arrival.request_bound_functions, line 109, characters 13-47
@taskset_respects_min_request_bound
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task ->
       JobCost Job -> arrival_sequence Job -> MinRequestBound Task -> TaskSet (Equality.sort Task) -> Prop
```

Body:

```coq
taskset_respects_min_request_bound =
fun (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (H0 : JobCost Job)
  (arr_seq : arrival_sequence Job) (H2 : MinRequestBound Task) (ts : TaskSet (Equality.sort Task)) =>
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
@respects_min_request_bound Task Job H H0 arr_seq tsk (@min_request_bound Task H2 tsk)
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task ->
       JobCost Job -> arrival_sequence Job -> MinRequestBound Task -> TaskSet (Equality.sort Task) -> Prop

Arguments taskset_respects_min_request_bound {Task Job H H0} arr_seq {H2} ts
```

## Lean

```lean
@Prosa.Model.Task.Arrival.RequestBoundFunctions.taskset_respects_min_request_bound : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobCost Job] →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              [Prosa.Model.Task.Arrival.RequestBoundFunctions.MinRequestBound Task] →
                Prosa.Model.Task.Concept.TaskSet Task → Prop
def Prosa.Model.Task.Arrival.RequestBoundFunctions.taskset_respects_min_request_bound.{u_1, u_2} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Behavior.Job.JobCost Job] →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              [Prosa.Model.Task.Arrival.RequestBoundFunctions.MinRequestBound Task] →
                Prosa.Model.Task.Concept.TaskSet Task → Prop :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task]
    [Prosa.Behavior.Job.JobCost Job] arr_seq [Prosa.Model.Task.Arrival.RequestBoundFunctions.MinRequestBound Task] ts =>
  ∀ (tsk : Task),
    decide (tsk ∈ ts) = true →
      Prosa.Model.Task.Arrival.RequestBoundFunctions.respects_min_request_bound arr_seq tsk
        (Prosa.Model.Task.Arrival.RequestBoundFunctions.min_request_bound tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_RequestBoundFunctions_taskset_respects_min_request_bound
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
       Prosa_Model_Task_Arrival_RequestBoundFunctions_MinRequestBound Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskSet Task -> SProp
```

Body:

```coq
Prosa_Model_Task_Arrival_RequestBoundFunctions_taskset_respects_min_request_bound@{u_1 u_2 Lean.u_1+1.0
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
  (inst_19 : 
   Prosa_Model_Task_Arrival_RequestBoundFunctions_MinRequestBound Task
     inst_3)
  (ts : Prosa_Model_Task_Concept_TaskSet Task) =>
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
Prosa_Model_Task_Arrival_RequestBoundFunctions_respects_min_request_bound Task
  inst_3 Job
  inst_7
  inst_10
  inst_14 arr_seq tsk
  (Prosa_Model_Task_Arrival_RequestBoundFunctions_MinRequestBound_min_request_bound Task
     inst_3
     inst_19 tsk)
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
       Prosa_Model_Task_Arrival_RequestBoundFunctions_MinRequestBound Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskSet Task -> SProp

Arguments Prosa_Model_Task_Arrival_RequestBoundFunctions_taskset_respects_min_request_bound 
  Task inst_3 
  Job inst_7
  inst_10
  inst_14 
  arr_seq inst_19 
  ts
```
