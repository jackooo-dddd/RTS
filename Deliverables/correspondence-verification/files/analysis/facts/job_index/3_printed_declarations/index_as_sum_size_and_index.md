# `index_as_sum_size_and_index`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.job_index.index_as_sum_size_and_index`
- Lean: `Prosa.Analysis.Facts.JobIndex.index_as_sum_size_and_index`
- Certificate: `index_as_sum_size_and_index_correspondence`

## Official Rocq

```coq
index_as_sum_size_and_index :
forall {Task : TaskType} {Job : JobType} {H : JobTask Job Task} {H0 : JobArrival Job}
  (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H0 arr_seq ->
forall j1 : Equality.sort Job,
@arrives_in Job arr_seq j1 ->
@job_index Task Job H0 H arr_seq j1 =
@size (Equality.sort Job) (@task_arrivals_before_job_arrival Job Task H H0 arr_seq j1) +
@index Job j1 (@task_arrivals_at_job_arrival Job Task H H0 arr_seq j1)

index_as_sum_size_and_index is not universe polymorphic
Arguments index_as_sum_size_and_index {Task Job H H0} arr_seq H_valid_arrival_sequence 
  j1 H_j1_from_arrival_sequence
index_as_sum_size_and_index is opaque
Expands to: Constant prosa.analysis.facts.job_index.index_as_sum_size_and_index
Declared in library prosa.analysis.facts.job_index, line 103, characters 8-35
@index_as_sum_size_and_index
     : forall (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (H0 : JobArrival Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H0 arr_seq ->
       forall j1 : Equality.sort Job,
       @arrives_in Job arr_seq j1 ->
       @job_index Task Job H0 H arr_seq j1 =
       @size (Equality.sort Job) (@task_arrivals_before_job_arrival Job Task H H0 arr_seq j1) +
       @index Job j1 (@task_arrivals_at_job_arrival Job Task H H0 arr_seq j1)
```

## Lean

```lean
@Prosa.Analysis.Facts.JobIndex.index_as_sum_size_and_index : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (j1 : Job),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j1 →
        Prosa.Model.Task.Arrivals.job_index arr_seq j1 =
          (Prosa.Model.Task.Arrivals.task_arrivals_before_job_arrival arr_seq j1).length +
            List.idxOf j1 (Prosa.Model.Task.Arrivals.task_arrivals_at_job_arrival arr_seq j1)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_JobIndex_index_as_sum_size_and_index
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : Prosa_Model_Task_Concept_JobTask
                                                                                Job
                                                                                inst_7
                                                                                Task
                                                                                inst_3)
         (inst_14 : Prosa_Behavior_Job_JobArrival
                                                                                Job
                                                                                inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_14 arr_seq ->
       forall j1 : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_7 arr_seq j1 ->
       @eq Nat
         (Prosa_Model_Task_Arrivals_job_index Task
            inst_3 Job
            inst_7
            inst_14
            inst_10 arr_seq j1)
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (List_length Job
               (Prosa_Model_Task_Arrivals_task_arrivals_before_job_arrival Job
                  inst_7 Task
                  inst_3
                  inst_10
                  inst_14 arr_seq j1))
            (List_idxOf Job
               (instBEqOfDecidableEq Job inst_7)
               j1
               (Prosa_Model_Task_Arrivals_task_arrivals_at_job_arrival Job
                  inst_7 Task
                  inst_3
                  inst_10
                  inst_14 arr_seq j1)))
```
