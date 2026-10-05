# `consecutive_job_separation`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.periodic.arrival_separation.consecutive_job_separation`
- Lean: `Prosa.Analysis.Facts.Periodic.ArrivalSeparation.consecutive_job_separation`
- Certificate: `consecutive_job_separation_correspondence`

## Official Rocq

```coq
consecutive_job_separation :
forall {Task : TaskType} {H : PeriodicModel Task} {Job : JobType} {H0 : JobTask Job Task}
  {H1 : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall tsk : Equality.sort Task,
@respects_periodic_task_model Task H Job H0 H1 arr_seq tsk ->
is_true (@valid_period Task H tsk) ->
forall j1 j2 : Equality.sort Job,
@arrives_in Job arr_seq j1 ->
@arrives_in Job arr_seq j2 ->
@job_task Job Task H0 j1 = tsk ->
@job_task Job Task H0 j2 = tsk ->
@job_index Task Job H1 H0 arr_seq j2 = @job_index Task Job H1 H0 arr_seq j1 + 1 ->
@job_arrival Job H1 j2 = @job_arrival Job H1 j1 + @task_period Task H tsk

consecutive_job_separation is not universe polymorphic
Arguments consecutive_job_separation {Task H Job H0 H1} arr_seq H_valid_arrival_sequence 
  tsk H_periodic_model H_valid_period j1 j2 H_j1_from_arr_seq H_j2_from_arr_seq H_j1_of_task 
  H_j2_of_task H_consecutive_jobs
consecutive_job_separation is opaque
Expands to: Constant prosa.analysis.facts.periodic.arrival_separation.consecutive_job_separation
Declared in library prosa.analysis.facts.periodic.arrival_separation, line 46, characters 10-36
@consecutive_job_separation
     : forall (Task : TaskType) (H : PeriodicModel Task) (Job : JobType) (H0 : JobTask Job Task)
         (H1 : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall tsk : Equality.sort Task,
       @respects_periodic_task_model Task H Job H0 H1 arr_seq tsk ->
       is_true (@valid_period Task H tsk) ->
       forall j1 j2 : Equality.sort Job,
       @arrives_in Job arr_seq j1 ->
       @arrives_in Job arr_seq j2 ->
       @job_task Job Task H0 j1 = tsk ->
       @job_task Job Task H0 j2 = tsk ->
       @job_index Task Job H1 H0 arr_seq j2 = @job_index Task Job H1 H0 arr_seq j1 + 1 ->
       @job_arrival Job H1 j2 = @job_arrival Job H1 j1 + @task_period Task H tsk
```

## Lean

```lean
@Prosa.Analysis.Facts.Periodic.ArrivalSeparation.consecutive_job_separation : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  [inst_1 : Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (tsk : Task),
      Prosa.Model.Task.Arrival.Periodic.respects_periodic_task_model arr_seq tsk →
        Prosa.Model.Task.Arrival.Periodic.valid_period tsk = true →
          ∀ (j1 j2 : Job),
            Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j1 →
              Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j2 →
                Prosa.Model.Task.Concept.job_task j1 = tsk →
                  Prosa.Model.Task.Concept.job_task j2 = tsk →
                    Prosa.Model.Task.Arrivals.job_index arr_seq j2 =
                        Prosa.Model.Task.Arrivals.job_index arr_seq j1 + 1 →
                      Prosa.Behavior.Job.job_arrival j2 =
                        Prosa.Behavior.Job.job_arrival j1 + Prosa.Model.Task.Arrival.Periodic.task_period tsk
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Periodic_ArrivalSeparation_consecutive_job_separation
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : 
          DecidableEq Job)
         (inst_13 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_10 Task
            inst_3)
         (inst_17 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_10)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_10),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_10
         inst_17 arr_seq ->
       forall tsk : Task,
       Prosa_Model_Task_Arrival_Periodic_respects_periodic_task_model Task
         inst_3
         inst_6 Job
         inst_10
         inst_13
         inst_17 arr_seq tsk ->
       @eq Bool
         (Prosa_Model_Task_Arrival_Periodic_valid_period Task
            inst_3
            inst_6 tsk)
         Bool_true ->
       forall j1 j2 : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_10 arr_seq j1 ->
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_10 arr_seq j2 ->
       @eq Task
         (Prosa_Model_Task_Concept_JobTask_job_task Job
            inst_10 Task
            inst_3
            inst_13 j1)
         tsk ->
       @eq Task
         (Prosa_Model_Task_Concept_JobTask_job_task Job
            inst_10 Task
            inst_3
            inst_13 j2)
         tsk ->
       @eq Nat
         (Prosa_Model_Task_Arrivals_job_index Task
            inst_3 Job
            inst_10
            inst_17
            inst_13 arr_seq j2)
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (Prosa_Model_Task_Arrivals_job_index Task
               inst_3 Job
               inst_10
               inst_17
               inst_13 arr_seq
               j1)
            (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))) ->
       @eq Prosa_Behavior_Time_instant
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_10
            inst_17 j2)
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
            (Prosa_Behavior_Job_JobArrival_job_arrival Job
               inst_10
               inst_17 j1)
            (Prosa_Model_Task_Arrival_Periodic_PeriodicModel_task_period Task
               inst_3
               inst_6 tsk))
```
