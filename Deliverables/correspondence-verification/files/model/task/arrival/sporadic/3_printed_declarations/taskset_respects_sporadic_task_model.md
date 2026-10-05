# `taskset_respects_sporadic_task_model`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.arrival.sporadic.taskset_respects_sporadic_task_model`
- Lean: `Prosa.Model.Task.Arrival.Sporadic.taskset_respects_sporadic_task_model`
- Certificate: `sp_taskset_respects_sporadic_task_model_canonical`

## Official Rocq

```coq
taskset_respects_sporadic_task_model :
forall {Task : TaskType},
SporadicModel Task ->
TaskSet (Equality.sort Task) ->
forall {Job : JobType}, JobTask Job Task -> JobArrival Job -> arrival_sequence Job -> Prop

taskset_respects_sporadic_task_model is not universe polymorphic
Arguments taskset_respects_sporadic_task_model {Task H} ts {Job H0 H1} arr_seq
taskset_respects_sporadic_task_model is transparent
Expands to: Constant prosa.model.task.arrival.sporadic.taskset_respects_sporadic_task_model
Declared in library prosa.model.task.arrival.sporadic, line 65, characters 13-49
@taskset_respects_sporadic_task_model
     : forall Task : TaskType,
       SporadicModel Task ->
       TaskSet (Equality.sort Task) ->
       forall Job : JobType, JobTask Job Task -> JobArrival Job -> arrival_sequence Job -> Prop
```

Body:

```coq
taskset_respects_sporadic_task_model =
fun (Task : TaskType) (H : SporadicModel Task) (ts : TaskSet (Equality.sort Task)) 
  (Job : JobType) (H0 : JobTask Job Task) (H1 : JobArrival Job) (arr_seq : arrival_sequence Job) =>
forall tsk : Equality.sort Task,
is_true (tsk \in ts) -> @respects_sporadic_task_model Task H Job H0 H1 arr_seq tsk
     : forall {Task : TaskType},
       SporadicModel Task ->
       TaskSet (Equality.sort Task) ->
       forall {Job : JobType}, JobTask Job Task -> JobArrival Job -> arrival_sequence Job -> Prop

Arguments taskset_respects_sporadic_task_model {Task H} ts {Job H0 H1} arr_seq
```

## Lean

```lean
@Prosa.Model.Task.Arrival.Sporadic.taskset_respects_sporadic_task_model : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task] →
      Prosa.Model.Task.Concept.TaskSet Task →
        {Job : Prosa.Behavior.Job.JobType} →
          [inst_2 : DecidableEq Job] →
            [Prosa.Model.Task.Concept.JobTask Job Task] →
              [Prosa.Behavior.Job.JobArrival Job] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop
def Prosa.Model.Task.Arrival.Sporadic.taskset_respects_sporadic_task_model.{u_1, u_2} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task] →
      Prosa.Model.Task.Concept.TaskSet Task →
        {Job : Prosa.Behavior.Job.JobType} →
          [inst_2 : DecidableEq Job] →
            [Prosa.Model.Task.Concept.JobTask Job Task] →
              [Prosa.Behavior.Job.JobArrival Job] → Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task] ts {Job} [DecidableEq Job]
    [Prosa.Model.Task.Concept.JobTask Job Task] [Prosa.Behavior.Job.JobArrival Job] arr_seq =>
  ∀ (tsk : Task), decide (tsk ∈ ts) = true → Prosa.Model.Task.Arrival.Sporadic.respects_sporadic_task_model arr_seq tsk
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_Sporadic_taskset_respects_sporadic_task_model
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskSet Task ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_12 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_12 Task
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_12 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_12 ->
       SProp
```

Body:

```coq
Prosa_Model_Task_Arrival_Sporadic_taskset_respects_sporadic_task_model@{u_1 u_2 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Task_Arrival_Sporadic_SporadicModel
                                                                              Task
                                                                              inst_3)
  (ts : Prosa_Model_Task_Concept_TaskSet Task) (Job : Prosa_Behavior_Job_JobType)
  (inst_12 : DecidableEq Job)
  (inst_15 : Prosa_Model_Task_Concept_JobTask
                                                                               Job
                                                                               inst_12
                                                                               Task
                                                                               inst_3)
  (inst_19 : Prosa_Behavior_Job_JobArrival
                                                                               Job
                                                                               inst_12)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_12) =>
forall tsk : Task,
@eq Bool
  (Decidable_decide
     (Membership_mem Task (Prosa_Model_Task_Concept_TaskSet Task) (List_instMembership Task) ts tsk)
     (List_instDecidableMemOfLawfulBEq Task
        (instBEqOfDecidableEq Task inst_3)
        (instLawfulBEq Task inst_3) tsk ts))
  Bool_true ->
Prosa_Model_Task_Arrival_Sporadic_respects_sporadic_task_model Task
  inst_3
  inst_6 Job
  inst_12
  inst_15
  inst_19 arr_seq tsk
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskSet Task ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_12 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_12 Task
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_12 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_12 ->
       SProp

Arguments Prosa_Model_Task_Arrival_Sporadic_taskset_respects_sporadic_task_model 
  Task inst_3
  inst_6 ts Job
  inst_12
  inst_15
  inst_19 arr_seq
```
