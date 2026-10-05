# `periodic_model_respects_max_inter_arrival_model`

- Kind (Rocq): Remark
- Rocq: `prosa.analysis.facts.periodic.max_inter_arrival.periodic_model_respects_max_inter_arrival_model`
- Lean: `Prosa.Analysis.Facts.Periodic.MaxInterArrival.periodic_model_respects_max_inter_arrival_model`
- Certificate: `periodic_model_respects_max_inter_arrival_model_correspondence`

## Official Rocq

```coq
periodic_model_respects_max_inter_arrival_model :
forall {Task : TaskType} {H : PeriodicModel Task} {Job : JobType} {H0 : JobTask Job Task}
  {H1 : JobArrival Job} (arr_seq : arrival_sequence Job) (tsk : Equality.sort Task),
is_true (@valid_period Task H tsk) ->
@respects_periodic_task_model Task H Job H0 H1 arr_seq tsk ->
@valid_task_max_inter_arrival_time Task (@max_inter_eq_period Task H) Job H0 H1 arr_seq tsk

periodic_model_respects_max_inter_arrival_model is not universe polymorphic
Arguments periodic_model_respects_max_inter_arrival_model {Task H Job H0 H1} arr_seq tsk _ _
periodic_model_respects_max_inter_arrival_model is opaque
Expands to: Constant
            prosa.analysis.facts.periodic.max_inter_arrival.periodic_model_respects_max_inter_arrival_model
Declared in library prosa.analysis.facts.periodic.max_inter_arrival, line 33, characters 9-56
@periodic_model_respects_max_inter_arrival_model
     : forall (Task : TaskType) (H : PeriodicModel Task) (Job : JobType) (H0 : JobTask Job Task)
         (H1 : JobArrival Job) (arr_seq : arrival_sequence Job) (tsk : Equality.sort Task),
       is_true (@valid_period Task H tsk) ->
       @respects_periodic_task_model Task H Job H0 H1 arr_seq tsk ->
       @valid_task_max_inter_arrival_time Task (@max_inter_eq_period Task H) Job H0 H1 arr_seq tsk
```

## Lean

```lean
@Prosa.Analysis.Facts.Periodic.MaxInterArrival.periodic_model_respects_max_inter_arrival_model : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  [inst_1 : Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (tsk : Task),
  Prosa.Model.Task.Arrival.Periodic.valid_period tsk = true →
    Prosa.Model.Task.Arrival.Periodic.respects_periodic_task_model arr_seq tsk →
      Prosa.Model.Task.Arrival.Task_max_inter_arrival.valid_task_max_inter_arrival_time arr_seq tsk
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Periodic_MaxInterArrival_periodic_model_respects_max_inter_arrival_model
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
                      inst_10)
         (tsk : Task),
       @eq Bool
         (Prosa_Model_Task_Arrival_Periodic_valid_period Task
            inst_3
            inst_6 tsk)
         Bool_true ->
       Prosa_Model_Task_Arrival_Periodic_respects_periodic_task_model Task
         inst_3
         inst_6 Job
         inst_10
         inst_13
         inst_17 arr_seq tsk ->
       Prosa_Model_Task_Arrival_Task_max_inter_arrival_valid_task_max_inter_arrival_time Task
         inst_3
         (Prosa_Analysis_Facts_Periodic_MaxInterArrival_max_inter_eq_period Task
            inst_3
            inst_6)
         Job inst_10
         inst_13
         inst_17 arr_seq tsk
```
