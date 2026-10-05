# `all_jobs_arrive_within_hyperperiod`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.hyperperiod.all_jobs_arrive_within_hyperperiod`
- Lean: `Prosa.Analysis.Facts.Hyperperiod.all_jobs_arrive_within_hyperperiod`
- Certificate: `all_jobs_arrive_within_hyperperiod_correspondence`

## Official Rocq

```coq
all_jobs_arrive_within_hyperperiod :
forall {Task : TaskType} {H0 : PeriodicModel Task} {Job : JobType} {H1 : JobTask Job Task}
  {H2 : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H2 arr_seq ->
forall (ts : TaskSet (Equality.sort Task)) (tsk : Equality.sort Task) (j : Equality.sort Job) (t : instant),
is_true (j \in @jobs_in_hyperperiod Task H0 Job H1 ts arr_seq t tsk) ->
is_true (t <= @job_arrival Job H2 j < t + @hyperperiod Task H0 ts)

all_jobs_arrive_within_hyperperiod is not universe polymorphic
Arguments all_jobs_arrive_within_hyperperiod {Task H0 Job H1 H2} arr_seq H_valid_arrival_sequence 
  ts tsk j t _
all_jobs_arrive_within_hyperperiod is opaque
Expands to: Constant prosa.analysis.facts.hyperperiod.all_jobs_arrive_within_hyperperiod
Declared in library prosa.analysis.facts.hyperperiod, line 114, characters 8-42
@all_jobs_arrive_within_hyperperiod
     : forall (Task : TaskType) (H0 : PeriodicModel Task) (Job : JobType) (H1 : JobTask Job Task)
         (H2 : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H2 arr_seq ->
       forall (ts : TaskSet (Equality.sort Task)) (tsk : Equality.sort Task) (j : Equality.sort Job)
         (t : instant),
       is_true (j \in @jobs_in_hyperperiod Task H0 Job H1 ts arr_seq t tsk) ->
       is_true (t <= @job_arrival Job H2 j < t + @hyperperiod Task H0 ts)
```

## Lean

```lean
@Prosa.Analysis.Facts.Hyperperiod.all_jobs_arrive_within_hyperperiod : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (ts : Prosa.Model.Task.Concept.TaskSet Task) (tsk : Task) (j : Job) (t : Prosa.Behavior.Time.instant),
      decide (j ∈ Prosa.Analysis.Definitions.Hyperperiod.jobs_in_hyperperiod ts arr_seq t tsk) = true →
        (decide (t ≤ Prosa.Behavior.Job.job_arrival j) &&
            decide (Prosa.Behavior.Job.job_arrival j < t + Prosa.Analysis.Definitions.Hyperperiod.hyperperiod ts)) =
          true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Hyperperiod_all_jobs_arrive_within_hyperperiod
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
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
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_13),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_13
         inst_20 arr_seq ->
       forall (ts : Prosa_Model_Task_Concept_TaskSet Task) (tsk : Task) (j : Job)
         (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Decidable_decide
            (Membership_mem Job (List Job) (List_instMembership Job)
               (Prosa_Analysis_Definitions_Hyperperiod_jobs_in_hyperperiod Task
                  inst_3
                  inst_9 Job
                  inst_13
                  inst_16 ts arr_seq t tsk)
               j)
            (List_instDecidableMemOfLawfulBEq Job
               (instBEqOfDecidableEq Job
                  inst_13)
               (instLawfulBEq Job inst_13) j
               (Prosa_Analysis_Definitions_Hyperperiod_jobs_in_hyperperiod Task
                  inst_3
                  inst_9 Job
                  inst_13
                  inst_16 ts arr_seq t tsk)))
         Bool_true ->
       @eq Bool
         (Bool_and
            (Decidable_decide
               (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t
                  (Prosa_Behavior_Job_JobArrival_job_arrival Job
                     inst_13
                     inst_20 j))
               (Nat_decLe t
                  (Prosa_Behavior_Job_JobArrival_job_arrival Job
                     inst_13
                     inst_20 j)))
            (Decidable_decide
               (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat
                  (Prosa_Behavior_Job_JobArrival_job_arrival Job
                     inst_13
                     inst_20 j)
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t
                     (Prosa_Analysis_Definitions_Hyperperiod_hyperperiod Task
                        inst_3
                        inst_9 ts)))
               (Nat_decLt
                  (Prosa_Behavior_Job_JobArrival_job_arrival Job
                     inst_13
                     inst_20 j)
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t
                     (Prosa_Analysis_Definitions_Hyperperiod_hyperperiod Task
                        inst_3
                        inst_9 ts)))))
         Bool_true
```
