# `sporadic_task_arrivals_bound`

- Kind (Rocq): Theorem
- Rocq: `prosa.analysis.facts.sporadic.arrival_bound.sporadic_task_arrivals_bound`
- Lean: `Prosa.Analysis.Facts.Sporadic.ArrivalBound.sporadic_task_arrivals_bound`
- Certificate: `sporadic_task_arrivals_bound_correspondence`

## Official Rocq

```coq
sporadic_task_arrivals_bound :
forall {Task : TaskType} {H : SporadicModel Task} {Job : JobType} {H0 : JobTask Job Task}
  {H1 : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall tsk : Equality.sort Task,
@respects_sporadic_task_model Task H Job H0 H1 arr_seq tsk ->
is_true (@valid_task_min_inter_arrival_time Task H tsk) ->
forall t1 t2 : instant,
is_true
  (@number_of_task_arrivals Job Task H0 arr_seq tsk t1 t2 <= @max_sporadic_arrivals Task H tsk (t2 - t1))

sporadic_task_arrivals_bound is not universe polymorphic
Arguments sporadic_task_arrivals_bound {Task H Job H0 H1} arr_seq H_valid_arrival_sequence 
  tsk H_sporadic_model H_valid_inter_min_arrival t1 t2
sporadic_task_arrivals_bound is opaque
Expands to: Constant prosa.analysis.facts.sporadic.arrival_bound.sporadic_task_arrivals_bound
Declared in library prosa.analysis.facts.sporadic.arrival_bound, line 126, characters 10-38
@sporadic_task_arrivals_bound
     : forall (Task : TaskType) (H : SporadicModel Task) (Job : JobType) (H0 : JobTask Job Task)
         (H1 : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall tsk : Equality.sort Task,
       @respects_sporadic_task_model Task H Job H0 H1 arr_seq tsk ->
       is_true (@valid_task_min_inter_arrival_time Task H tsk) ->
       forall t1 t2 : instant,
       is_true
         (@number_of_task_arrivals Job Task H0 arr_seq tsk t1 t2 <=
          @max_sporadic_arrivals Task H tsk (t2 - t1))
```

## Lean

```lean
@Prosa.Analysis.Facts.Sporadic.ArrivalBound.sporadic_task_arrivals_bound : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (tsk : Task),
      Prosa.Model.Task.Arrival.Sporadic.respects_sporadic_task_model arr_seq tsk →
        Prosa.Model.Task.Arrival.Sporadic.valid_task_min_inter_arrival_time tsk = true →
          ∀ (t1 t2 : Prosa.Behavior.Time.instant),
            Prosa.Model.Task.Arrivals.number_of_task_arrivals arr_seq tsk t1 t2 ≤
              Prosa.Analysis.Facts.Sporadic.ArrivalBound.max_sporadic_arrivals tsk (t2 - t1)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Sporadic_ArrivalBound_sporadic_task_arrivals_bound
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
       forall t1 t2 : Prosa_Behavior_Time_instant,
       LE_le_inst1 Nat instLENat
         (Prosa_Model_Task_Arrivals_number_of_task_arrivals Job
            inst_10 Task
            inst_3
            inst_13 arr_seq tsk t1
            t2)
         (Prosa_Analysis_Facts_Sporadic_ArrivalBound_max_sporadic_arrivals Task
            inst_3
            inst_6 tsk
            (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
               Prosa_Behavior_Time_instant (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t2 t1))
```
