# `sporadic_arrival_curve_respects_max_arrivals`

- Kind (Rocq): Lemma
- Rocq: `prosa.model.task.arrival.sporadic_as_curve.sporadic_arrival_curve_respects_max_arrivals`
- Lean: `Prosa.Model.Task.Arrival.SporadicAsCurve.sporadic_arrival_curve_respects_max_arrivals`
- Certificate: `sporadic_arrival_curve_respects_max_arrivals_correspondence`

## Official Rocq

```coq
sporadic_arrival_curve_respects_max_arrivals :
forall {Task : TaskType} {H : SporadicModel Task} {Job : JobType} {H0 : JobTask Job Task}
  {H1 : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall tsk : Equality.sort Task,
@respects_sporadic_task_model Task H Job H0 H1 arr_seq tsk ->
is_true (@valid_task_min_inter_arrival_time Task H tsk) ->
@respects_max_arrivals Task Job H0 arr_seq tsk (@max_sporadic_arrivals Task H tsk)

sporadic_arrival_curve_respects_max_arrivals is not universe polymorphic
Arguments sporadic_arrival_curve_respects_max_arrivals {Task H Job H0 H1} arr_seq 
  H_valid_arrival_sequence tsk H_sporadic_model H_valid_inter_min_arrival t1 t2 _
sporadic_arrival_curve_respects_max_arrivals is opaque
Expands to: Constant prosa.model.task.arrival.sporadic_as_curve.sporadic_arrival_curve_respects_max_arrivals
Declared in library prosa.model.task.arrival.sporadic_as_curve, line 55, characters 10-54
@sporadic_arrival_curve_respects_max_arrivals
     : forall (Task : TaskType) (H : SporadicModel Task) (Job : JobType) (H0 : JobTask Job Task)
         (H1 : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall tsk : Equality.sort Task,
       @respects_sporadic_task_model Task H Job H0 H1 arr_seq tsk ->
       is_true (@valid_task_min_inter_arrival_time Task H tsk) ->
       @respects_max_arrivals Task Job H0 arr_seq tsk (@max_sporadic_arrivals Task H tsk)
```

## Lean

```lean
@Prosa.Model.Task.Arrival.SporadicAsCurve.sporadic_arrival_curve_respects_max_arrivals : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  [inst_1 : Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (tsk : Task),
      Prosa.Model.Task.Arrival.Sporadic.respects_sporadic_task_model arr_seq tsk →
        Prosa.Model.Task.Arrival.Sporadic.valid_task_min_inter_arrival_time tsk = true →
          Prosa.Model.Task.Arrival.Curves.respects_max_arrivals arr_seq tsk
            (Prosa.Analysis.Facts.Sporadic.ArrivalBound.max_sporadic_arrivals tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_SporadicAsCurve_sporadic_arrival_curve_respects_max_arrivals
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
       Prosa_Model_Task_Arrival_Curves_respects_max_arrivals Task
         inst_3 Job
         inst_10
         inst_13 arr_seq tsk
         (Prosa_Analysis_Facts_Sporadic_ArrivalBound_max_sporadic_arrivals Task
            inst_3
            inst_6 tsk)
```
