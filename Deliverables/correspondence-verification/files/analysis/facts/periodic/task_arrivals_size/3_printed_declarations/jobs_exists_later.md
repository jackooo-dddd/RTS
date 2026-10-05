# `jobs_exists_later`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.periodic.task_arrivals_size.jobs_exists_later`
- Lean: `Prosa.Analysis.Facts.Periodic.TaskArrivalsSize.jobs_exists_later`
- Certificate: `jobs_exists_later_correspondence`

## Official Rocq

```coq
jobs_exists_later :
forall {Task : TaskType} {H : TaskOffset Task} {H0 : PeriodicModel Task} {Job : JobType}
  {H1 : JobTask Job Task} {H2 : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H2 arr_seq ->
forall tsk : Equality.sort Task,
@valid_offset Task H Job H1 H2 arr_seq tsk ->
is_true (@valid_period Task H0 tsk) ->
@respects_periodic_task_model Task H0 Job H1 H2 arr_seq tsk ->
@infinite_jobs Task Job H1 H2 arr_seq ->
forall n : nat,
exists j : Equality.sort Job,
  @arrives_in Job arr_seq j /\
  @job_task Job Task H1 j = tsk /\
  @job_arrival Job H2 j = @task_offset Task H tsk + n * @task_period Task H0 tsk /\
  @job_index Task Job H2 H1 arr_seq j = n

jobs_exists_later is not universe polymorphic
Arguments jobs_exists_later {Task H H0 Job H1 H2} arr_seq H_valid_arrival_sequence 
  tsk H_valid_offset H_valid_period H_task_respects_periodic_model H_infinite_jobs 
  n%nat_scope
jobs_exists_later is opaque
Expands to: Constant prosa.analysis.facts.periodic.task_arrivals_size.jobs_exists_later
Declared in library prosa.analysis.facts.periodic.task_arrivals_size, line 109, characters 10-27
@jobs_exists_later
     : forall (Task : TaskType) (H : TaskOffset Task) (H0 : PeriodicModel Task) (Job : JobType)
         (H1 : JobTask Job Task) (H2 : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H2 arr_seq ->
       forall tsk : Equality.sort Task,
       @valid_offset Task H Job H1 H2 arr_seq tsk ->
       is_true (@valid_period Task H0 tsk) ->
       @respects_periodic_task_model Task H0 Job H1 H2 arr_seq tsk ->
       @infinite_jobs Task Job H1 H2 arr_seq ->
       forall n : nat,
       exists j : Equality.sort Job,
         @arrives_in Job arr_seq j /\
         @job_task Job Task H1 j = tsk /\
         @job_arrival Job H2 j = @task_offset Task H tsk + n * @task_period Task H0 tsk /\
         @job_index Task Job H2 H1 arr_seq j = n
```

## Lean

```lean
@Prosa.Analysis.Facts.Periodic.TaskArrivalsSize.jobs_exists_later : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Offset.TaskOffset Task]
  [inst_2 : Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_3 : DecidableEq Job] [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_5 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (tsk : Task),
      Prosa.Model.Task.Offset.valid_offset arr_seq tsk →
        Prosa.Model.Task.Arrival.Periodic.valid_period tsk = true →
          Prosa.Model.Task.Arrival.Periodic.respects_periodic_task_model arr_seq tsk →
            Prosa.Analysis.Definitions.InfiniteJobs.infinite_jobs arr_seq →
              ∀ (n : ℕ),
                ∃ j,
                  Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j ∧
                    Prosa.Model.Task.Concept.job_task j = tsk ∧
                      Prosa.Behavior.Job.job_arrival j =
                          Prosa.Model.Task.Offset.task_offset tsk +
                            n * Prosa.Model.Task.Arrival.Periodic.task_period tsk ∧
                        Prosa.Model.Task.Arrivals.job_index arr_seq j = n
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Periodic_TaskArrivalsSize_jobs_exists_later
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Offset_TaskOffset Task
            inst_3)
         (inst_9 : 
          Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_13 : 
          DecidableEq Job)
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
       forall tsk : Task,
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
       forall n : Nat,
       Exists Job
         (fun j : Job =>
          And
            (Prosa_Behavior_Arrival_sequence_arrives_in Job
               inst_13 arr_seq j)
            (And
               (@eq Task
                  (Prosa_Model_Task_Concept_JobTask_job_task Job
                     inst_13
                     Task inst_3
                     inst_16 j)
                  tsk)
               (And
                  (@eq Prosa_Behavior_Time_instant
                     (Prosa_Behavior_Job_JobArrival_job_arrival Job
                        inst_13
                        inst_20
                        j)
                     (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
                        (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
                        (Prosa_Model_Task_Offset_TaskOffset_task_offset Task
                           inst_3
                           inst_6
                           tsk)
                        (HMul_hMul_inst7 Nat Prosa_Behavior_Time_duration Nat (instHMul_inst1 Nat instMulNat)
                           n
                           (Prosa_Model_Task_Arrival_Periodic_PeriodicModel_task_period Task
                              inst_3
                              inst_9
                              tsk))))
                  (@eq Nat
                     (Prosa_Model_Task_Arrivals_job_index Task
                        inst_3
                        Job
                        inst_13
                        inst_20
                        inst_16
                        arr_seq j)
                     n))))
```
