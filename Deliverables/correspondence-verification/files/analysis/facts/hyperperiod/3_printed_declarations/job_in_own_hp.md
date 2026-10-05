# `job_in_own_hp`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.hyperperiod.job_in_own_hp`
- Lean: `Prosa.Analysis.Facts.Hyperperiod.job_in_own_hp`
- Certificate: `job_in_own_hp_correspondence`

## Official Rocq

```coq
job_in_own_hp :
forall {Task : TaskType} {H : TaskOffset Task} {H0 : PeriodicModel Task} {Job : JobType}
  {H1 : JobTask Job Task} {H2 : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H2 arr_seq ->
forall ts : TaskSet (Equality.sort Task),
@valid_periods Task H0 ts ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
is_true (@valid_period Task H0 tsk) ->
forall j1 j2 : Equality.sort Job,
@arrives_in Job arr_seq j1 ->
@job_task Job Task H1 j1 = tsk ->
is_true (@max_task_offset Task H ts <= @job_arrival Job H2 j1) ->
is_true (@max_task_offset Task H ts <= @job_arrival Job H2 j2) ->
is_true
  (j1
     \in @jobs_in_hyperperiod Task H0 Job H1 ts arr_seq
           ((@job_arrival Job H2 j1 - @max_task_offset Task H ts) %/ @hyperperiod Task H0 ts *
            @hyperperiod Task H0 ts + @max_task_offset Task H ts)
           tsk)

job_in_own_hp is not universe polymorphic
Arguments job_in_own_hp {Task H H0 Job H1 H2} arr_seq H_valid_arrival_sequence ts 
  H_valid_periods tsk H_task_in_ts H_valid_period j1 j2 H_j1_from_arr_seq H_j1_task 
  H_j1_arr_after_O_max H_j2_arr_after_O_max
job_in_own_hp is opaque
Expands to: Constant prosa.analysis.facts.hyperperiod.job_in_own_hp
Declared in library prosa.analysis.facts.hyperperiod, line 202, characters 8-21
@job_in_own_hp
     : forall (Task : TaskType) (H : TaskOffset Task) (H0 : PeriodicModel Task) (Job : JobType)
         (H1 : JobTask Job Task) (H2 : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H2 arr_seq ->
       forall ts : TaskSet (Equality.sort Task),
       @valid_periods Task H0 ts ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       is_true (@valid_period Task H0 tsk) ->
       forall j1 j2 : Equality.sort Job,
       @arrives_in Job arr_seq j1 ->
       @job_task Job Task H1 j1 = tsk ->
       is_true (@max_task_offset Task H ts <= @job_arrival Job H2 j1) ->
       is_true (@max_task_offset Task H ts <= @job_arrival Job H2 j2) ->
       is_true
         (j1
            \in @jobs_in_hyperperiod Task H0 Job H1 ts arr_seq
                  ((@job_arrival Job H2 j1 - @max_task_offset Task H ts) %/ @hyperperiod Task H0 ts *
                   @hyperperiod Task H0 ts + @max_task_offset Task H ts)
                  tsk)
```

## Lean

```lean
@Prosa.Analysis.Facts.Hyperperiod.job_in_own_hp : ∀ {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  [inst_1 : Prosa.Model.Task.Offset.TaskOffset Task] [inst_2 : Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_3 : DecidableEq Job] [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_5 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (ts : Prosa.Model.Task.Concept.TaskSet Task),
      Prosa.Model.Task.Arrival.Periodic.valid_periods ts →
        ∀ (tsk : Task),
          decide (tsk ∈ ts) = true →
            Prosa.Model.Task.Arrival.Periodic.valid_period tsk = true →
              ∀ (j1 j2 : Job),
                Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j1 →
                  Prosa.Model.Task.Concept.job_task j1 = tsk →
                    Prosa.Model.Task.Offset.max_task_offset ts ≤ Prosa.Behavior.Job.job_arrival j1 →
                      Prosa.Model.Task.Offset.max_task_offset ts ≤ Prosa.Behavior.Job.job_arrival j2 →
                        decide
                            (j1 ∈
                              Prosa.Analysis.Definitions.Hyperperiod.jobs_in_hyperperiod ts arr_seq
                                ((Prosa.Behavior.Job.job_arrival j1 - Prosa.Model.Task.Offset.max_task_offset ts) /
                                      Prosa.Analysis.Definitions.Hyperperiod.hyperperiod ts *
                                    Prosa.Analysis.Definitions.Hyperperiod.hyperperiod ts +
                                  Prosa.Model.Task.Offset.max_task_offset ts)
                                tsk) =
                          true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Hyperperiod_job_in_own_hp
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
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_13),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_13
         inst_20 arr_seq ->
       forall ts : Prosa_Model_Task_Concept_TaskSet Task,
       Prosa_Model_Task_Arrival_Periodic_valid_periods Task
         inst_3
         inst_9 ts ->
       forall tsk : Task,
       @eq Bool
         (Decidable_decide
            (Membership_mem Task (Prosa_Model_Task_Concept_TaskSet Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_3)
               (instLawfulBEq Task inst_3) tsk
               ts))
         Bool_true ->
       @eq Bool
         (Prosa_Model_Task_Arrival_Periodic_valid_period Task
            inst_3
            inst_9 tsk)
         Bool_true ->
       forall j1 j2 : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_13 arr_seq j1 ->
       @eq Task
         (Prosa_Model_Task_Concept_JobTask_job_task Job
            inst_13 Task
            inst_3
            inst_16 j1)
         tsk ->
       LE_le_inst1 Nat instLENat
         (Prosa_Model_Task_Offset_max_task_offset Task
            inst_3
            inst_6 ts)
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_13
            inst_20 j1) ->
       LE_le_inst1 Nat instLENat
         (Prosa_Model_Task_Offset_max_task_offset Task
            inst_3
            inst_6 ts)
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_13
            inst_20 j2) ->
       @eq Bool
         (Decidable_decide
            (Membership_mem Job (List Job) (List_instMembership Job)
               (Prosa_Analysis_Definitions_Hyperperiod_jobs_in_hyperperiod Task
                  inst_3
                  inst_9 Job
                  inst_13
                  inst_16 ts arr_seq
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
                     (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
                     (HMul_hMul_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                        Prosa_Behavior_Time_instant (instHMul_inst1 Prosa_Behavior_Time_instant instMulNat)
                        (HDiv_hDiv_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                           Prosa_Behavior_Time_instant
                           (instHDiv_inst1 Prosa_Behavior_Time_instant Nat_instDiv)
                           (HSub_hSub_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
                              (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
                              (Prosa_Behavior_Job_JobArrival_job_arrival Job
                                 inst_13
                                 inst_20 j1)
                              (Prosa_Model_Task_Offset_max_task_offset Task
                                 inst_3
                                 inst_6 ts))
                           (Prosa_Analysis_Definitions_Hyperperiod_hyperperiod Task
                              inst_3
                              inst_9 ts))
                        (Prosa_Analysis_Definitions_Hyperperiod_hyperperiod Task
                           inst_3
                           inst_9 ts))
                     (Prosa_Model_Task_Offset_max_task_offset Task
                        inst_3
                        inst_6 ts))
                  tsk)
               j1)
            (List_instDecidableMemOfLawfulBEq Job
               (instBEqOfDecidableEq Job
                  inst_13)
               (instLawfulBEq Job inst_13) j1
               (Prosa_Analysis_Definitions_Hyperperiod_jobs_in_hyperperiod Task
                  inst_3
                  inst_9 Job
                  inst_13
                  inst_16 ts arr_seq
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
                     (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
                     (HMul_hMul_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                        Prosa_Behavior_Time_instant (instHMul_inst1 Prosa_Behavior_Time_instant instMulNat)
                        (HDiv_hDiv_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                           Prosa_Behavior_Time_instant
                           (instHDiv_inst1 Prosa_Behavior_Time_instant Nat_instDiv)
                           (HSub_hSub_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
                              (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
                              (Prosa_Behavior_Job_JobArrival_job_arrival Job
                                 inst_13
                                 inst_20 j1)
                              (Prosa_Model_Task_Offset_max_task_offset Task
                                 inst_3
                                 inst_6 ts))
                           (Prosa_Analysis_Definitions_Hyperperiod_hyperperiod Task
                              inst_3
                              inst_9 ts))
                        (Prosa_Analysis_Definitions_Hyperperiod_hyperperiod Task
                           inst_3
                           inst_9 ts))
                     (Prosa_Model_Task_Offset_max_task_offset Task
                        inst_3
                        inst_6 ts))
                  tsk)))
         Bool_true
```
