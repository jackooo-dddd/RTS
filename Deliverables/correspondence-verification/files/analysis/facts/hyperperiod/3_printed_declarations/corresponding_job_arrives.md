# `corresponding_job_arrives`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.hyperperiod.corresponding_job_arrives`
- Lean: `Prosa.Analysis.Facts.Hyperperiod.corresponding_job_arrives`
- Certificate: `corresponding_job_arrives_correspondence`

## Official Rocq

```coq
corresponding_job_arrives :
forall {Task : TaskType} {H : TaskOffset Task} {H0 : PeriodicModel Task} {Job : JobType}
  {H1 : JobTask Job Task} {H2 : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H2 arr_seq ->
forall ts : TaskSet (Equality.sort Task),
@valid_periods Task H0 ts ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
@valid_offset Task H Job H1 H2 arr_seq tsk ->
is_true (@valid_period Task H0 tsk) ->
@respects_periodic_task_model Task H0 Job H1 H2 arr_seq tsk ->
@infinite_jobs Task Job H1 H2 arr_seq ->
forall j1 j2 : Equality.sort Job,
@arrives_in Job arr_seq j1 ->
@job_task Job Task H1 j1 = tsk ->
is_true (@max_task_offset Task H ts <= @job_arrival Job H2 j1) ->
is_true (@max_task_offset Task H ts <= @job_arrival Job H2 j2) ->
@arrives_in Job arr_seq
  (@corresponding_job_in_hyperperiod Task H H0 Job H1 H2 ts arr_seq j1
     (@starting_instant_of_corresponding_hyperperiod Task H H0 Job H2 ts j2) tsk)

corresponding_job_arrives is not universe polymorphic
Arguments corresponding_job_arrives {Task H H0 Job H1 H2} arr_seq H_valid_arrival_sequence 
  ts H_valid_periods tsk H_task_in_ts H_valid_offset H_valid_period H_periodic_task 
  H_infinite_jobs j1 j2 H_j1_from_arr_seq H_j1_task H_j1_arr_after_O_max H_j2_arr_after_O_max
corresponding_job_arrives is opaque
Expands to: Constant prosa.analysis.facts.hyperperiod.corresponding_job_arrives
Declared in library prosa.analysis.facts.hyperperiod, line 235, characters 8-33
@corresponding_job_arrives
     : forall (Task : TaskType) (H : TaskOffset Task) (H0 : PeriodicModel Task) (Job : JobType)
         (H1 : JobTask Job Task) (H2 : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H2 arr_seq ->
       forall ts : TaskSet (Equality.sort Task),
       @valid_periods Task H0 ts ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       @valid_offset Task H Job H1 H2 arr_seq tsk ->
       is_true (@valid_period Task H0 tsk) ->
       @respects_periodic_task_model Task H0 Job H1 H2 arr_seq tsk ->
       @infinite_jobs Task Job H1 H2 arr_seq ->
       forall j1 j2 : Equality.sort Job,
       @arrives_in Job arr_seq j1 ->
       @job_task Job Task H1 j1 = tsk ->
       is_true (@max_task_offset Task H ts <= @job_arrival Job H2 j1) ->
       is_true (@max_task_offset Task H ts <= @job_arrival Job H2 j2) ->
       @arrives_in Job arr_seq
         (@corresponding_job_in_hyperperiod Task H H0 Job H1 H2 ts arr_seq j1
            (@starting_instant_of_corresponding_hyperperiod Task H H0 Job H2 ts j2) tsk)
```

## Lean

```lean
@Prosa.Analysis.Facts.Hyperperiod.corresponding_job_arrives : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Offset.TaskOffset Task]
  [inst_2 : Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_3 : DecidableEq Job] [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_5 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (ts : Prosa.Model.Task.Concept.TaskSet Task),
      Prosa.Model.Task.Arrival.Periodic.valid_periods ts →
        ∀ (tsk : Task),
          decide (tsk ∈ ts) = true →
            Prosa.Model.Task.Offset.valid_offset arr_seq tsk →
              Prosa.Model.Task.Arrival.Periodic.valid_period tsk = true →
                Prosa.Model.Task.Arrival.Periodic.respects_periodic_task_model arr_seq tsk →
                  Prosa.Analysis.Definitions.InfiniteJobs.infinite_jobs arr_seq →
                    ∀ (j1 j2 : Job),
                      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j1 →
                        Prosa.Model.Task.Concept.job_task j1 = tsk →
                          Prosa.Model.Task.Offset.max_task_offset ts ≤ Prosa.Behavior.Job.job_arrival j1 →
                            Prosa.Model.Task.Offset.max_task_offset ts ≤ Prosa.Behavior.Job.job_arrival j2 →
                              Prosa.Behavior.Arrival_sequence.arrives_in arr_seq
                                (Prosa.Analysis.Definitions.Hyperperiod.corresponding_job_in_hyperperiod ts arr_seq j1
                                  (Prosa.Analysis.Definitions.Hyperperiod.starting_instant_of_corresponding_hyperperiod
                                    ts j2)
                                  tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Hyperperiod_corresponding_job_arrives
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
       Prosa_Model_Task_Offset_valid_offset Task
         inst_3
         inst_6 Job
         inst_13
         inst_16
         inst_20 arr_seq tsk ->
       @eq Bool
         (Prosa_Model_Task_Arrival_Periodic_valid_period Task
            inst_3
            inst_9 tsk)
         Bool_true ->
       Prosa_Model_Task_Arrival_Periodic_respects_periodic_task_model Task
         inst_3
         inst_9 Job
         inst_13
         inst_16
         inst_20 arr_seq tsk ->
       Prosa_Analysis_Definitions_InfiniteJobs_infinite_jobs Task
         inst_3 Job
         inst_13
         inst_16
         inst_20 arr_seq ->
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
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_13 arr_seq
         (Prosa_Analysis_Definitions_Hyperperiod_corresponding_job_in_hyperperiod Task
            inst_3
            inst_6
            inst_9 Job
            inst_13
            inst_16
            inst_20 ts arr_seq j1
            (Prosa_Analysis_Definitions_Hyperperiod_starting_instant_of_corresponding_hyperperiod Task
               inst_3
               inst_6
               inst_9 Job
               inst_13
               inst_20 ts j2)
            tsk)
```
