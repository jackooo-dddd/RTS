# `valid_task_arrival_sequence_from_taskset`

- Kind (Rocq): Lemma
- Rocq: `prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence_from_taskset`
- Lean: `Prosa.Model.Composite.ValidTaskArrivalSequence.valid_task_arrival_sequence_from_taskset`
- Certificate: `valid_task_arrival_sequence_from_taskset_correspondence`

## Official Rocq

```coq
valid_task_arrival_sequence_from_taskset :
forall {Task : TaskType} {H : TaskCost Task} {H0 : MaxArrivals Task} {Job : JobType} 
  {H1 : JobTask Job Task} {H2 : JobCost Job} {H3 : JobArrival Job} (ts : seq (Equality.sort Task))
  (arr_seq : arrival_sequence Job),
@valid_task_arrival_sequence Task H H0 Job H1 H2 H3 ts arr_seq ->
@all_jobs_from_taskset Task Job H1 arr_seq ts

valid_task_arrival_sequence_from_taskset is not universe polymorphic
Arguments valid_task_arrival_sequence_from_taskset {Task H H0 Job H1 H2 H3} ts%seq_scope arr_seq _ j _
valid_task_arrival_sequence_from_taskset is opaque
Expands to: Constant
            prosa.model.composite.valid_task_arrival_sequence.valid_task_arrival_sequence_from_taskset
Declared in library prosa.model.composite.valid_task_arrival_sequence, line 53, characters 8-48
@valid_task_arrival_sequence_from_taskset
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (Job : JobType)
         (H1 : JobTask Job Task) (H2 : JobCost Job) (H3 : JobArrival Job) (ts : seq (Equality.sort Task))
         (arr_seq : arrival_sequence Job),
       @valid_task_arrival_sequence Task H H0 Job H1 H2 H3 ts arr_seq ->
       @all_jobs_from_taskset Task Job H1 arr_seq ts
```

## Lean

```lean
@Prosa.Model.Composite.ValidTaskArrivalSequence.valid_task_arrival_sequence_from_taskset : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_3 : DecidableEq Job] [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_5 : Prosa.Behavior.Job.JobCost Job] [inst_6 : Prosa.Behavior.Job.JobArrival Job] (ts : List Task)
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Model.Composite.ValidTaskArrivalSequence.valid_task_arrival_sequence ts arr_seq →
    Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts
```

## Lean, imported into Rocq

```coq
Prosa_Model_Composite_ValidTaskArrivalSequence_valid_task_arrival_sequence_from_taskset
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_9 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_13 : 
          DecidableEq Job)
         (inst_16 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_13 Task
            inst_3)
         (inst_20 : 
          Prosa_Behavior_Job_JobCost Job
            inst_13)
         (inst_23 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_13)
         (ts : List Task)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_13),
       Prosa_Model_Composite_ValidTaskArrivalSequence_valid_task_arrival_sequence Task
         inst_3
         inst_6
         inst_9 Job
         inst_13
         inst_16
         inst_20
         inst_23 ts arr_seq ->
       Prosa_Model_Task_Concept_all_jobs_from_taskset Task
         inst_3 Job
         inst_13
         inst_16 arr_seq ts
```
