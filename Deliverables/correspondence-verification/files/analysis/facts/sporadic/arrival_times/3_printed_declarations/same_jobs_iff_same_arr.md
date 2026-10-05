# `same_jobs_iff_same_arr`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.sporadic.arrival_times.same_jobs_iff_same_arr`
- Lean: `Prosa.Analysis.Facts.Sporadic.ArrivalTimes.same_jobs_iff_same_arr`
- Certificate: `same_jobs_iff_same_arr_correspondence`

## Official Rocq

```coq
same_jobs_iff_same_arr :
forall {Task : TaskType} {H : SporadicModel Task} {Job : JobType} {H0 : JobTask Job Task}
  {H1 : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall tsk : Equality.sort Task,
@respects_sporadic_task_model Task H Job H0 H1 arr_seq tsk ->
is_true (@valid_task_min_inter_arrival_time Task H tsk) ->
forall j1 j2 : Equality.sort Job,
@arrives_in Job arr_seq j1 ->
@arrives_in Job arr_seq j2 ->
@job_task Job Task H0 j1 = tsk ->
@job_task Job Task H0 j2 = tsk -> j1 = j2 <-> @job_arrival Job H1 j1 = @job_arrival Job H1 j2

same_jobs_iff_same_arr is not universe polymorphic
Arguments same_jobs_iff_same_arr {Task H Job H0 H1} arr_seq H_valid_arrival_sequence 
  tsk H_sporadic_model H_valid_inter_min_arrival j1 j2 H_j1_from_arrseq H_j2_from_arrseq 
  H_j1_task H_j2_task
same_jobs_iff_same_arr is opaque
Expands to: Constant prosa.analysis.facts.sporadic.arrival_times.same_jobs_iff_same_arr
Declared in library prosa.analysis.facts.sporadic.arrival_times, line 63, characters 8-30
@same_jobs_iff_same_arr
     : forall (Task : TaskType) (H : SporadicModel Task) (Job : JobType) (H0 : JobTask Job Task)
         (H1 : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall tsk : Equality.sort Task,
       @respects_sporadic_task_model Task H Job H0 H1 arr_seq tsk ->
       is_true (@valid_task_min_inter_arrival_time Task H tsk) ->
       forall j1 j2 : Equality.sort Job,
       @arrives_in Job arr_seq j1 ->
       @arrives_in Job arr_seq j2 ->
       @job_task Job Task H0 j1 = tsk ->
       @job_task Job Task H0 j2 = tsk -> j1 = j2 <-> @job_arrival Job H1 j1 = @job_arrival Job H1 j2
```

## Lean

```lean
@Prosa.Analysis.Facts.Sporadic.ArrivalTimes.same_jobs_iff_same_arr : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (tsk : Task),
      Prosa.Model.Task.Arrival.Sporadic.respects_sporadic_task_model arr_seq tsk →
        Prosa.Model.Task.Arrival.Sporadic.valid_task_min_inter_arrival_time tsk = true →
          ∀ (j1 j2 : Job),
            Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j1 →
              Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j2 →
                Prosa.Model.Task.Concept.job_task j1 = tsk →
                  Prosa.Model.Task.Concept.job_task j2 = tsk →
                    (j1 = j2 ↔ Prosa.Behavior.Job.job_arrival j1 = Prosa.Behavior.Job.job_arrival j2)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Sporadic_ArrivalTimes_same_jobs_iff_same_arr
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Arrival_Sporadic_SporadicModel Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job)
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
       Iff (@eq Job j1 j2)
         (@eq Prosa_Behavior_Time_instant
            (Prosa_Behavior_Job_JobArrival_job_arrival Job
               inst_10
               inst_17 j1)
            (Prosa_Behavior_Job_JobArrival_job_arrival Job
               inst_10
               inst_17 j2))
```
