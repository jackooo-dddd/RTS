# `taskset_respects_min_separation`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.arrival.curves.taskset_respects_min_separation`
- Lean: `Prosa.Model.Task.Arrival.Curves.taskset_respects_min_separation`
- Certificate: `taskset_respects_min_separation_correspondence`

## Official Rocq

```coq
taskset_respects_min_separation :
forall {Task : TaskType} {Job : JobType},
JobTask Job Task -> arrival_sequence Job -> MinSeparation Task -> TaskSet (Equality.sort Task) -> Prop

taskset_respects_min_separation is not universe polymorphic
Arguments taskset_respects_min_separation {Task Job H} arr_seq {H3} ts
taskset_respects_min_separation is transparent
Expands to: Constant prosa.model.task.arrival.curves.taskset_respects_min_separation
Declared in library prosa.model.task.arrival.curves, line 150, characters 13-44
@taskset_respects_min_separation
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task -> arrival_sequence Job -> MinSeparation Task -> TaskSet (Equality.sort Task) -> Prop
```

Body:

```coq
taskset_respects_min_separation =
fun (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (arr_seq : arrival_sequence Job)
  (H3 : MinSeparation Task) (ts : TaskSet (Equality.sort Task)) =>
forall tsk : Equality.sort Task,
is_true (tsk \in ts) -> @respects_min_separation Task Job H arr_seq tsk (@min_separation Task H3 tsk)
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task -> arrival_sequence Job -> MinSeparation Task -> TaskSet (Equality.sort Task) -> Prop

Arguments taskset_respects_min_separation {Task Job H} arr_seq {H3} ts
```

## Lean

```lean
@Prosa.Model.Task.Arrival.Curves.taskset_respects_min_separation : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
            [Prosa.Model.Task.Arrival.Curves.MinSeparation Task] → Prosa.Model.Task.Concept.TaskSet Task → Prop
def Prosa.Model.Task.Arrival.Curves.taskset_respects_min_separation.{u_1, u_2} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
            [Prosa.Model.Task.Arrival.Curves.MinSeparation Task] → Prosa.Model.Task.Concept.TaskSet Task → Prop :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task] arr_seq
    [Prosa.Model.Task.Arrival.Curves.MinSeparation Task] ts =>
  ∀ (tsk : Task),
    decide (tsk ∈ ts) = true →
      Prosa.Model.Task.Arrival.Curves.respects_min_separation arr_seq tsk
        (Prosa.Model.Task.Arrival.Curves.min_separation tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_Curves_taskset_respects_min_separation
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Prosa_Model_Task_Arrival_Curves_MinSeparation Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskSet Task -> SProp
```

Body:

```coq
Prosa_Model_Task_Arrival_Curves_taskset_respects_min_separation@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
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
  (inst_16 : Prosa_Model_Task_Arrival_Curves_MinSeparation
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
Prosa_Model_Task_Arrival_Curves_respects_min_separation Task
  inst_3 Job
  inst_7
  inst_10 arr_seq tsk
  (Prosa_Model_Task_Arrival_Curves_MinSeparation_min_separation Task
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
       Prosa_Model_Task_Arrival_Curves_MinSeparation Task
         inst_3 ->
       Prosa_Model_Task_Concept_TaskSet Task -> SProp

Arguments Prosa_Model_Task_Arrival_Curves_taskset_respects_min_separation Task
  inst_3 Job
  inst_7
  inst_10 arr_seq
  inst_16 ts
```
