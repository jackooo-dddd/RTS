# `only_j_at_job_arrival_j`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.sporadic.arrival_sequence.only_j_at_job_arrival_j`
- Lean: `Prosa.Analysis.Facts.Sporadic.ArrivalSequence.only_j_at_job_arrival_j`
- Certificate: `only_j_at_job_arrival_j_correspondence`

## Official Rocq

```coq
only_j_at_job_arrival_j :
forall {Task : TaskType} {H : SporadicModel Task} {Job : JobType} {H0 : JobTask Job Task}
  {H1 : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall tsk : Equality.sort Task,
@respects_sporadic_task_model Task H Job H0 H1 arr_seq tsk ->
is_true (@valid_task_min_inter_arrival_time Task H tsk) ->
forall j1 : Equality.sort Job,
@arrives_in Job arr_seq j1 ->
@job_task Job Task H0 j1 = tsk ->
forall t : instant, @job_arrival Job H1 j1 = t -> @task_arrivals_at Job Task H0 arr_seq tsk t = [:: j1]

only_j_at_job_arrival_j is not universe polymorphic
Arguments only_j_at_job_arrival_j {Task H Job H0 H1} arr_seq H_valid_arrival_sequence 
  tsk H_sporadic_model H_valid_inter_min_arrival j1 H_j1_from_arrival_sequence H_j1_task 
  t _
only_j_at_job_arrival_j is opaque
Expands to: Constant prosa.analysis.facts.sporadic.arrival_sequence.only_j_at_job_arrival_j
Declared in library prosa.analysis.facts.sporadic.arrival_sequence, line 81, characters 8-31
@only_j_at_job_arrival_j
     : forall (Task : TaskType) (H : SporadicModel Task) (Job : JobType) (H0 : JobTask Job Task)
         (H1 : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall tsk : Equality.sort Task,
       @respects_sporadic_task_model Task H Job H0 H1 arr_seq tsk ->
       is_true (@valid_task_min_inter_arrival_time Task H tsk) ->
       forall j1 : Equality.sort Job,
       @arrives_in Job arr_seq j1 ->
       @job_task Job Task H0 j1 = tsk ->
       forall t : instant,
       @job_arrival Job H1 j1 = t -> @task_arrivals_at Job Task H0 arr_seq tsk t = [:: j1]
```

## Lean

```lean
@Prosa.Analysis.Facts.Sporadic.ArrivalSequence.only_j_at_job_arrival_j : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (tsk : Task),
      Prosa.Model.Task.Arrival.Sporadic.respects_sporadic_task_model arr_seq tsk →
        Prosa.Model.Task.Arrival.Sporadic.valid_task_min_inter_arrival_time tsk = true →
          ∀ (j1 : Job),
            Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j1 →
              Prosa.Model.Task.Concept.job_task j1 = tsk →
                ∀ (t : Prosa.Behavior.Time.instant),
                  Prosa.Behavior.Job.job_arrival j1 = t →
                    Prosa.Model.Task.Arrivals.task_arrivals_at arr_seq tsk t = [j1]
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Sporadic_ArrivalSequence_only_j_at_job_arrival_j
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
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
       Prosa_Model_Task_Arrival_Sporadic_respects_sporadic_task_model Task
         inst_3
         inst_6 Job
         inst_10
         inst_13
         inst_17 arr_seq tsk ->
       @eq Bool
         (Prosa_Model_Task_Arrival_Sporadic_valid_task_min_inter_arrival_time Task
            inst_3
            inst_6 tsk)
         Bool_true ->
       forall j1 : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_10 arr_seq j1 ->
       @eq Task
         (Prosa_Model_Task_Concept_JobTask_job_task Job
            inst_10 Task
            inst_3
            inst_13 j1)
         tsk ->
       forall t : Prosa_Behavior_Time_instant,
       @eq Prosa_Behavior_Time_instant
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_10
            inst_17 j1)
         t ->
       @eq (List Job)
         (Prosa_Model_Task_Arrivals_task_arrivals_at Job
            inst_10 Task
            inst_3
            inst_13 arr_seq tsk t)
         (List_cons Job j1 (List_nil Job))
```
