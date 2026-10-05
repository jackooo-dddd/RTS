# `job_costs_shifted_valid`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.shifted_job_costs.job_costs_shifted_valid`
- Lean: `Prosa.Analysis.Facts.ShiftedJobCosts.job_costs_shifted_valid`
- Certificate: `job_costs_shifted_valid_correspondence`

## Official Rocq

```coq
job_costs_shifted_valid :
forall {Task : TaskType} {H : TaskOffset Task} {H0 : PeriodicModel Task} {H1 : TaskCost Task} 
  {Job : JobType} {H2 : JobTask Job Task} {H3 : JobArrival Job} {H4 : JobCost Job}
  (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H3 arr_seq ->
@arrivals_have_valid_job_costs Task H1 Job H2 H4 arr_seq ->
forall ts : TaskSet (Equality.sort Task),
@taskset_respects_periodic_task_model Task H0 Job H2 H3 arr_seq ts ->
@valid_periods Task H0 ts ->
@valid_offsets Task H Job H2 H3 arr_seq ts ->
forall j : Equality.sort Job,
@infinite_jobs Task Job H2 H3 arr_seq ->
@all_jobs_from_taskset Task Job H2 arr_seq ts ->
@arrivals_have_valid_job_costs Task H1 Job H2 (@job_costs_in_oi Task H H0 Job H2 H3 H4 arr_seq ts j) arr_seq

job_costs_shifted_valid is not universe polymorphic
Arguments job_costs_shifted_valid {Task H H0 H1 Job H2 H3 H4} arr_seq H_valid_arrival_sequence
  H_arrivals_have_valid_job_costs ts H_periodic_taskset H_valid_periods_in_taskset 
  H_valid_offsets_in_taskset j H_infinite_jobs H_jobs_from_taskset j _
job_costs_shifted_valid is opaque
Expands to: Constant prosa.analysis.facts.shifted_job_costs.job_costs_shifted_valid
Declared in library prosa.analysis.facts.shifted_job_costs, line 68, characters 8-31
@job_costs_shifted_valid
     : forall (Task : TaskType) (H : TaskOffset Task) (H0 : PeriodicModel Task) (H1 : TaskCost Task)
         (Job : JobType) (H2 : JobTask Job Task) (H3 : JobArrival Job) (H4 : JobCost Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H3 arr_seq ->
       @arrivals_have_valid_job_costs Task H1 Job H2 H4 arr_seq ->
       forall ts : TaskSet (Equality.sort Task),
       @taskset_respects_periodic_task_model Task H0 Job H2 H3 arr_seq ts ->
       @valid_periods Task H0 ts ->
       @valid_offsets Task H Job H2 H3 arr_seq ts ->
       forall j : Equality.sort Job,
       @infinite_jobs Task Job H2 H3 arr_seq ->
       @all_jobs_from_taskset Task Job H2 arr_seq ts ->
       @arrivals_have_valid_job_costs Task H1 Job H2 (@job_costs_in_oi Task H H0 Job H2 H3 H4 arr_seq ts j)
         arr_seq
```

## Lean

```lean
@Prosa.Analysis.Facts.ShiftedJobCosts.job_costs_shifted_valid : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Offset.TaskOffset Task]
  [inst_2 : Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_3 : DecidableEq Job] [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_5 : Prosa.Behavior.Job.JobArrival Job] [inst_6 : Prosa.Behavior.Job.JobCost Job]
  [inst_7 : Prosa.Model.Task.Concept.TaskCost Task] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
      ∀ (ts : Prosa.Model.Task.Concept.TaskSet Task),
        Prosa.Model.Task.Arrival.Periodic.taskset_respects_periodic_task_model arr_seq ts →
          Prosa.Model.Task.Arrival.Periodic.valid_periods ts →
            Prosa.Model.Task.Offset.valid_offsets arr_seq ts →
              ∀ (j : Job),
                Prosa.Analysis.Definitions.InfiniteJobs.infinite_jobs arr_seq →
                  Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
                    Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_ShiftedJobCosts_job_costs_shifted_valid
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Offset_TaskOffset Task
            inst_3)
         (inst_9 : 
          Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_13 : DecidableEq Job)
         (inst_16 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_13 Task
            inst_3)
         (inst_20 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_13)
         (inst_23 : 
          Prosa_Behavior_Job_JobCost Job
            inst_13)
         (inst_26 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_13),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_13
         inst_20 arr_seq ->
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_26 Job
         inst_13
         inst_16
         inst_23 arr_seq ->
       forall ts : Prosa_Model_Task_Concept_TaskSet Task,
       Prosa_Model_Task_Arrival_Periodic_taskset_respects_periodic_task_model Task
         inst_3
         inst_9 Job
         inst_13
         inst_16
         inst_20 arr_seq ts ->
       Prosa_Model_Task_Arrival_Periodic_valid_periods Task
         inst_3
         inst_9 ts ->
       Prosa_Model_Task_Offset_valid_offsets Task
         inst_3
         inst_6 Job
         inst_13
         inst_16
         inst_20 arr_seq ts ->
       forall j : Job,
       Prosa_Analysis_Definitions_InfiniteJobs_infinite_jobs Task
         inst_3 Job
         inst_13
         inst_16
         inst_20 arr_seq ->
       Prosa_Model_Task_Concept_all_jobs_from_taskset Task
         inst_3 Job
         inst_13
         inst_16 arr_seq ts ->
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_26 Job
         inst_13
         inst_16
         (Prosa_Analysis_Facts_ShiftedJobCosts_job_costs_in_oi Task
            inst_3
            inst_6
            inst_9 Job
            inst_13
            inst_16
            inst_20
            inst_23 arr_seq ts j)
         arr_seq
```
