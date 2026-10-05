# `arrival_of_nth_job`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.sporadic.arrival_bound.arrival_of_nth_job`
- Lean: `Prosa.Analysis.Facts.Sporadic.ArrivalBound.arrival_of_nth_job`
- Certificate: `arrival_of_nth_job_correspondence`

## Official Rocq

```coq
arrival_of_nth_job :
forall {Task : TaskType} {H : SporadicModel Task} {Job : JobType} {H0 : JobTask Job Task}
  {H1 : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall tsk : Equality.sort Task,
@respects_sporadic_task_model Task H Job H0 H1 arr_seq tsk ->
is_true (@valid_task_min_inter_arrival_time Task H tsk) ->
forall (dummy : Equality.sort Job) (t1 t2 : instant) (n i : nat) (j : Equality.sort Job),
n = @number_of_task_arrivals Job Task H0 arr_seq tsk t1 t2 ->
is_true (i < n) ->
j = @nth (Equality.sort Job) dummy (@task_arrivals_between Job Task H0 arr_seq tsk t1 t2) i ->
is_true (t1 + @task_min_inter_arrival_time Task H tsk * i <= @job_arrival Job H1 j)

arrival_of_nth_job is not universe polymorphic
Arguments arrival_of_nth_job {Task H Job H0 H1} arr_seq H_valid_arrival_sequence 
  tsk H_sporadic_model H_valid_inter_min_arrival dummy t1 t2 (n i)%nat_scope j _ 
  _ _
arrival_of_nth_job is opaque
Expands to: Constant prosa.analysis.facts.sporadic.arrival_bound.arrival_of_nth_job
Declared in library prosa.analysis.facts.sporadic.arrival_bound, line 49, characters 10-28
@arrival_of_nth_job
     : forall (Task : TaskType) (H : SporadicModel Task) (Job : JobType) (H0 : JobTask Job Task)
         (H1 : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall tsk : Equality.sort Task,
       @respects_sporadic_task_model Task H Job H0 H1 arr_seq tsk ->
       is_true (@valid_task_min_inter_arrival_time Task H tsk) ->
       forall (dummy : Equality.sort Job) (t1 t2 : instant) (n i : nat) (j : Equality.sort Job),
       n = @number_of_task_arrivals Job Task H0 arr_seq tsk t1 t2 ->
       is_true (i < n) ->
       j = @nth (Equality.sort Job) dummy (@task_arrivals_between Job Task H0 arr_seq tsk t1 t2) i ->
       is_true (t1 + @task_min_inter_arrival_time Task H tsk * i <= @job_arrival Job H1 j)
```

## Lean

```lean
@Prosa.Analysis.Facts.Sporadic.ArrivalBound.arrival_of_nth_job : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (tsk : Task),
      Prosa.Model.Task.Arrival.Sporadic.respects_sporadic_task_model arr_seq tsk →
        Prosa.Model.Task.Arrival.Sporadic.valid_task_min_inter_arrival_time tsk = true →
          ∀ (dummy : Job) (t1 t2 : Prosa.Behavior.Time.instant) (n i : ℕ) (j : Job),
            n = Prosa.Model.Task.Arrivals.number_of_task_arrivals arr_seq tsk t1 t2 →
              i < n →
                j = (Prosa.Model.Task.Arrivals.task_arrivals_between arr_seq tsk t1 t2).getD i dummy →
                  t1 + Prosa.Model.Task.Arrival.Sporadic.task_min_inter_arrival_time tsk * i ≤
                    Prosa.Behavior.Job.job_arrival j
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Sporadic_ArrivalBound_arrival_of_nth_job
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
       forall (dummy : Job) (t1 t2 : Prosa_Behavior_Time_instant) (n i : Nat) (j : Job),
       @eq Nat n
         (Prosa_Model_Task_Arrivals_number_of_task_arrivals Job
            inst_10 Task
            inst_3
            inst_13 arr_seq tsk t1
            t2) ->
       LT_lt_inst1 Nat instLTNat i n ->
       @eq Job j
         (List_getD Job
            (Prosa_Model_Task_Arrivals_task_arrivals_between Job
               inst_10 Task
               inst_3
               inst_13 arr_seq tsk
               t1 t2)
            i dummy) ->
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
            (HMul_hMul_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
               (instHMul_inst1 Prosa_Behavior_Time_duration instMulNat)
               (Prosa_Model_Task_Arrival_Sporadic_SporadicModel_task_min_inter_arrival_time Task
                  inst_3
                  inst_6 tsk)
               i))
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_10
            inst_17 j)
```
