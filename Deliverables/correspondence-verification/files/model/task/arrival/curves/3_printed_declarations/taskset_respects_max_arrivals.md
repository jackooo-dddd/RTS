# `taskset_respects_max_arrivals`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.arrival.curves.taskset_respects_max_arrivals`
- Lean: `Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals`
- Certificate: `taskset_respects_max_arrivals_correspondence`

## Official Rocq

```coq
taskset_respects_max_arrivals :
forall {Task : TaskType} {Job : JobType},
JobTask Job Task -> arrival_sequence Job -> MaxArrivals Task -> TaskSet (Equality.sort Task) -> Prop

taskset_respects_max_arrivals is not universe polymorphic
Arguments taskset_respects_max_arrivals {Task Job H} arr_seq {H0} ts
taskset_respects_max_arrivals is transparent
Expands to: Constant prosa.model.task.arrival.curves.taskset_respects_max_arrivals
Declared in library prosa.model.task.arrival.curves, line 138, characters 13-42
@taskset_respects_max_arrivals
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task -> arrival_sequence Job -> MaxArrivals Task -> TaskSet (Equality.sort Task) -> Prop
```

Body:

```coq
taskset_respects_max_arrivals =
fun (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (arr_seq : arrival_sequence Job)
  (H0 : MaxArrivals Task) (ts : TaskSet (Equality.sort Task)) =>
forall tsk : Equality.sort Task,
is_true (tsk \in ts) -> @respects_max_arrivals Task Job H arr_seq tsk (@max_arrivals Task H0 tsk)
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task -> arrival_sequence Job -> MaxArrivals Task -> TaskSet (Equality.sort Task) -> Prop

Arguments taskset_respects_max_arrivals {Task Job H} arr_seq {H0} ts
```

## Lean

```lean
@Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
            [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → Prosa.Model.Task.Concept.TaskSet Task → Prop
def Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals.{u_1, u_2} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
            [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] → Prosa.Model.Task.Concept.TaskSet Task → Prop :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task] arr_seq
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] ts =>
  ∀ (tsk : Task),
    decide (tsk ∈ ts) = true →
      Prosa.Model.Task.Arrival.Curves.respects_max_arrivals arr_seq tsk
        (Prosa.Model.Task.Arrival.Curves.max_arrivals tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskSet Task -> SProp
```

Body:

```coq
Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_7 : DecidableEq Job)
  (inst_10 : Prosa_Model_Task_Concept_JobTask
                                                                             Job
                                                                             inst_7
                                                                             Task
                                                                             inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_7)
  (inst_16 : Prosa_Model_Task_Arrival_Curves_MaxArrivals
                                                                             Task
                                                                             inst_3)
  (ts : Prosa_Model_Task_Concept_TaskSet Task) =>
forall tsk : Task,
@eq Bool
  (Decidable_decide
     (Membership_mem Task (Prosa_Model_Task_Concept_TaskSet Task) (List_instMembership Task) ts tsk)
     (List_instDecidableMemOfLawfulBEq Task
        (instBEqOfDecidableEq Task inst_3)
        (instLawfulBEq Task inst_3) tsk ts))
  Bool_true ->
Prosa_Model_Task_Arrival_Curves_respects_max_arrivals Task
  inst_3 Job
  inst_7
  inst_10 arr_seq tsk
  (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
     inst_3
     inst_16 tsk)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskSet Task -> SProp

Arguments Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
  inst_3 Job
  inst_7
  inst_10 arr_seq
  inst_16 ts
```
