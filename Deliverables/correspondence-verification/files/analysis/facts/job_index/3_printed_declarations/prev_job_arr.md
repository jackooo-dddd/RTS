# `prev_job_arr`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.job_index.prev_job_arr`
- Lean: `Prosa.Analysis.Facts.JobIndex.prev_job_arr`
- Certificate: `prev_job_arr_correspondence`

## Official Rocq

```coq
prev_job_arr :
forall {Task : TaskType} {Job : JobType} {H : JobTask Job Task} {H0 : JobArrival Job}
  (arr_seq : arrival_sequence Job) (j : Equality.sort Job),
@arrives_in Job arr_seq j -> @arrives_in Job arr_seq (@prev_job Job Task H H0 arr_seq j)

prev_job_arr is not universe polymorphic
Arguments prev_job_arr {Task Job H H0} arr_seq j H_arrives_in_arr_seq
prev_job_arr is opaque
Expands to: Constant prosa.analysis.facts.job_index.prev_job_arr
Declared in library prosa.analysis.facts.job_index, line 256, characters 8-20
@prev_job_arr
     : forall (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (H0 : JobArrival Job)
         (arr_seq : arrival_sequence Job) (j : Equality.sort Job),
       @arrives_in Job arr_seq j -> @arrives_in Job arr_seq (@prev_job Job Task H H0 arr_seq j)
```

## Lean

```lean
@Prosa.Analysis.Facts.JobIndex.prev_job_arr : ∀ {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_3 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (j : Job),
  Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
    Prosa.Behavior.Arrival_sequence.arrives_in arr_seq (Prosa.Model.Task.Arrivals.prev_job arr_seq j)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_JobIndex_prev_job_arr
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
                      inst_7)
         (j : Job),
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_7 arr_seq j ->
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_7 arr_seq
         (Prosa_Model_Task_Arrivals_prev_job Job
            inst_7 Task
            inst_3
            inst_10
            inst_14 arr_seq j)
```
