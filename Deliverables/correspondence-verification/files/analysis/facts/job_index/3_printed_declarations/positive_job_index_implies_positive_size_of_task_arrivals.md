# `positive_job_index_implies_positive_size_of_task_arrivals`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.job_index.positive_job_index_implies_positive_size_of_task_arrivals`
- Lean: `Prosa.Analysis.Facts.JobIndex.positive_job_index_implies_positive_size_of_task_arrivals`
- Certificate: `positive_job_index_implies_positive_size_of_task_arrivals_correspondence`

## Official Rocq

```coq
positive_job_index_implies_positive_size_of_task_arrivals :
forall {Task : TaskType} {Job : JobType} {H : JobTask Job Task} {H0 : JobArrival Job}
  (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H0 arr_seq ->
forall j1 : Equality.sort Job,
@arrives_in Job arr_seq j1 ->
is_true (0 < @size (Equality.sort Job) (@task_arrivals_up_to_job_arrival Job Task H H0 arr_seq j1))

positive_job_index_implies_positive_size_of_task_arrivals is not universe polymorphic
Arguments positive_job_index_implies_positive_size_of_task_arrivals {Task Job H H0} 
  arr_seq H_valid_arrival_sequence j1 H_j1_from_arrival_sequence
positive_job_index_implies_positive_size_of_task_arrivals is opaque
Expands to: Constant prosa.analysis.facts.job_index.positive_job_index_implies_positive_size_of_task_arrivals
Declared in library prosa.analysis.facts.job_index, line 221, characters 8-65
@positive_job_index_implies_positive_size_of_task_arrivals
     : forall (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (H0 : JobArrival Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H0 arr_seq ->
       forall j1 : Equality.sort Job,
       @arrives_in Job arr_seq j1 ->
       is_true (0 < @size (Equality.sort Job) (@task_arrivals_up_to_job_arrival Job Task H H0 arr_seq j1))
```

## Lean

```lean
@Prosa.Analysis.Facts.JobIndex.positive_job_index_implies_positive_size_of_task_arrivals : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_3 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (j1 : Job),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j1 →
        0 < (Prosa.Model.Task.Arrivals.task_arrivals_up_to_job_arrival arr_seq j1).length
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_JobIndex_positive_job_index_implies_positive_size_of_task_arrivals
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
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (List_length Job
            (Prosa_Model_Task_Arrivals_task_arrivals_up_to_job_arrival Job
               inst_7 Task
               inst_3
               inst_10
               inst_14 arr_seq j1))
```
