# `sporadic_task_sets_respects_max_arrivals`

- Kind (Rocq): Remark
- Rocq: `prosa.model.task.arrival.sporadic_as_curve.sporadic_task_sets_respects_max_arrivals`
- Lean: `Prosa.Model.Task.Arrival.SporadicAsCurve.sporadic_task_sets_respects_max_arrivals`
- Certificate: `sporadic_task_sets_respects_max_arrivals_correspondence`

## Official Rocq

```coq
sporadic_task_sets_respects_max_arrivals :
forall {Task : TaskType} {H : SporadicModel Task} {Job : JobType} {H0 : JobTask Job Task}
  {H1 : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall ts : TaskSet (Equality.sort Task),
@valid_taskset_inter_arrival_times Task H ts ->
@taskset_respects_sporadic_task_model Task H ts Job H0 H1 arr_seq ->
@taskset_respects_max_arrivals Task Job H0 arr_seq (@MaxArrivalsSporadic Task H) ts

sporadic_task_sets_respects_max_arrivals is not universe polymorphic
Arguments sporadic_task_sets_respects_max_arrivals {Task H Job H0 H1} arr_seq H_valid_arrival_sequence 
  ts _ _ tsk _ t1 t2 _
sporadic_task_sets_respects_max_arrivals is opaque
Expands to: Constant prosa.model.task.arrival.sporadic_as_curve.sporadic_task_sets_respects_max_arrivals
Declared in library prosa.model.task.arrival.sporadic_as_curve, line 63, characters 9-49
@sporadic_task_sets_respects_max_arrivals
     : forall (Task : TaskType) (H : SporadicModel Task) (Job : JobType) (H0 : JobTask Job Task)
         (H1 : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall ts : TaskSet (Equality.sort Task),
       @valid_taskset_inter_arrival_times Task H ts ->
       @taskset_respects_sporadic_task_model Task H ts Job H0 H1 arr_seq ->
       @taskset_respects_max_arrivals Task Job H0 arr_seq (@MaxArrivalsSporadic Task H) ts
```

## Lean

```lean
@Prosa.Model.Task.Arrival.SporadicAsCurve.sporadic_task_sets_respects_max_arrivals : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  [inst_1 : Prosa.Model.Task.Arrival.Sporadic.SporadicModel Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (ts : Prosa.Model.Task.Concept.TaskSet Task),
      Prosa.Model.Task.Arrival.Sporadic.valid_taskset_inter_arrival_times ts →
        Prosa.Model.Task.Arrival.Sporadic.taskset_respects_sporadic_task_model ts arr_seq →
          Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_SporadicAsCurve_sporadic_task_sets_respects_max_arrivals
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
       forall ts : Prosa_Model_Task_Concept_TaskSet Task,
       Prosa_Model_Task_Arrival_Sporadic_valid_taskset_inter_arrival_times Task
         inst_3
         inst_6 ts ->
       Prosa_Model_Task_Arrival_Sporadic_taskset_respects_sporadic_task_model Task
         inst_3
         inst_6 ts Job
         inst_10
         inst_13
         inst_17 arr_seq ->
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_10
         inst_13 arr_seq
         (Prosa_Model_Task_Arrival_SporadicAsCurve_MaxArrivalsSporadic Task
            inst_3
            inst_6)
         ts
```
