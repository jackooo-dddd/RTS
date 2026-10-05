# `prev_job_task`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.job_index.prev_job_task`
- Lean: `Prosa.Analysis.Facts.JobIndex.prev_job_task`
- Certificate: `prev_job_task_correspondence`

## Official Rocq

```coq
prev_job_task :
forall {Task : TaskType} {Job : JobType} {H : JobTask Job Task} {H0 : JobArrival Job}
  (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H0 arr_seq ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (0 < @job_index Task Job H0 H arr_seq j) ->
@job_task Job Task H (@prev_job Job Task H H0 arr_seq j) = @job_task Job Task H j

prev_job_task is not universe polymorphic
Arguments prev_job_task {Task Job H H0} arr_seq H_valid_arrival_sequence j H_arrives_in_arr_seq
  H_positive_job_index
prev_job_task is opaque
Expands to: Constant prosa.analysis.facts.job_index.prev_job_task
Declared in library prosa.analysis.facts.job_index, line 276, characters 8-21
@prev_job_task
     : forall (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (H0 : JobArrival Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H0 arr_seq ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (0 < @job_index Task Job H0 H arr_seq j) ->
       @job_task Job Task H (@prev_job Job Task H H0 arr_seq j) = @job_task Job Task H j
```

## Lean

```lean
@Prosa.Analysis.Facts.JobIndex.prev_job_task : ∀ {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_3 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (j : Job),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        0 < Prosa.Model.Task.Arrivals.job_index arr_seq j →
          Prosa.Model.Task.Concept.job_task (Prosa.Model.Task.Arrivals.prev_job arr_seq j) =
            Prosa.Model.Task.Concept.job_task j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_JobIndex_prev_job_task
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
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_7 arr_seq j ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (Prosa_Model_Task_Arrivals_job_index Task
            inst_3 Job
            inst_7
            inst_14
            inst_10 arr_seq j) ->
       @eq Task
         (Prosa_Model_Task_Concept_JobTask_job_task Job
            inst_7 Task
            inst_3
            inst_10
            (Prosa_Model_Task_Arrivals_prev_job Job
               inst_7 Task
               inst_3
               inst_10
               inst_14 arr_seq j))
         (Prosa_Model_Task_Concept_JobTask_job_task Job
            inst_7 Task
            inst_3
            inst_10 j)
```
