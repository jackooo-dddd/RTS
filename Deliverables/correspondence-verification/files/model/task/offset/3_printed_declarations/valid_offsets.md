# `valid_offsets`

- Kind (Rocq): Definition
- Rocq: `prosa.model.task.offset.valid_offsets`
- Lean: `Prosa.Model.Task.Offset.valid_offsets`
- Certificate: `valid_offsets_correspondence`

## Official Rocq

```coq
valid_offsets :
forall {Task : TaskType},
TaskOffset Task ->
forall {Job : JobType},
JobTask Job Task -> JobArrival Job -> arrival_sequence Job -> TaskSet (Equality.sort Task) -> Prop

valid_offsets is not universe polymorphic
Arguments valid_offsets {Task H Job H0 H1} arr_seq ts
valid_offsets is transparent
Expands to: Constant prosa.model.task.offset.valid_offsets
Declared in library prosa.model.task.offset, line 50, characters 13-26
@valid_offsets
     : forall Task : TaskType,
       TaskOffset Task ->
       forall Job : JobType,
       JobTask Job Task -> JobArrival Job -> arrival_sequence Job -> TaskSet (Equality.sort Task) -> Prop
```

Body:

```coq
valid_offsets =
fun (Task : TaskType) (H : TaskOffset Task) (Job : JobType) (H0 : JobTask Job Task) 
  (H1 : JobArrival Job) (arr_seq : arrival_sequence Job) (ts : TaskSet (Equality.sort Task)) =>
forall tsk : Equality.sort Task, is_true (tsk \in ts) -> @valid_offset Task H Job H0 H1 arr_seq tsk
     : forall {Task : TaskType},
       TaskOffset Task ->
       forall {Job : JobType},
       JobTask Job Task -> JobArrival Job -> arrival_sequence Job -> TaskSet (Equality.sort Task) -> Prop

Arguments valid_offsets {Task H Job H0 H1} arr_seq ts
```

## Lean

```lean
@Prosa.Model.Task.Offset.valid_offsets : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Offset.TaskOffset Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            [Prosa.Behavior.Job.JobArrival Job] →
              Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prosa.Model.Task.Concept.TaskSet Task → Prop
```

Body:

```lean
def Prosa.Model.Task.Offset.valid_offsets.{u_1, u_2} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Offset.TaskOffset Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            [Prosa.Behavior.Job.JobArrival Job] →
              Prosa.Behavior.Arrival_sequence.arrival_sequence Job → Prosa.Model.Task.Concept.TaskSet Task → Prop :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Offset.TaskOffset Task] {Job} [DecidableEq Job]
    [Prosa.Model.Task.Concept.JobTask Job Task] [Prosa.Behavior.Job.JobArrival Job] arr_seq ts =>
  ∀ (tsk : Task), decide (tsk ∈ ts) = true → Prosa.Model.Task.Offset.valid_offset arr_seq tsk
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Offset_valid_offsets
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Offset_TaskOffset Task inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job inst_10
         Task inst_3 ->
       Prosa_Behavior_Job_JobArrival Job inst_10 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_10 ->
       Prosa_Model_Task_Concept_TaskSet Task -> SProp
```

Body:

```coq
Prosa_Model_Task_Offset_valid_offsets@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.u_1+2.0
Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Task_Offset_TaskOffset Task
                                                                    inst_3)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_10 : DecidableEq Job)
  (inst_13 : Prosa_Model_Task_Concept_JobTask Job
                                                                     inst_10
                                                                     Task
                                                                     inst_3)
  (inst_17 : Prosa_Behavior_Job_JobArrival Job
                                                                     inst_10)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_10)
  (ts : Prosa_Model_Task_Concept_TaskSet Task) =>
forall tsk : Task,
@eq Bool
  (Decidable_decide
     (Membership_mem Task (Prosa_Model_Task_Concept_TaskSet Task) (List_instMembership Task) ts tsk)
     (List_instDecidableMemOfLawfulBEq Task
        (instBEqOfDecidableEq Task inst_3)
        (instLawfulBEq Task inst_3) tsk ts))
  Bool_true ->
Prosa_Model_Task_Offset_valid_offset Task inst_3
  inst_6 Job
  inst_10
  inst_13
  inst_17 arr_seq tsk
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Offset_TaskOffset Task inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job inst_10
         Task inst_3 ->
       Prosa_Behavior_Job_JobArrival Job inst_10 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_10 ->
       Prosa_Model_Task_Concept_TaskSet Task -> SProp

Arguments Prosa_Model_Task_Offset_valid_offsets Task
  inst_3
  inst_6 Job
  inst_10
  inst_13
  inst_17 arr_seq ts
```
