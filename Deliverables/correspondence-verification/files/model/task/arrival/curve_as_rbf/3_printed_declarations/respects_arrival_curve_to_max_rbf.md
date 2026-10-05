# `respects_arrival_curve_to_max_rbf`

- Kind (Rocq): Theorem
- Rocq: `prosa.model.task.arrival.curve_as_rbf.respects_arrival_curve_to_max_rbf`
- Lean: `Prosa.Model.Task.Arrival.CurveAsRbf.respects_arrival_curve_to_max_rbf`
- Certificate: `respects_arrival_curve_to_max_rbf_correspondence`

## Official Rocq

```coq
respects_arrival_curve_to_max_rbf :
forall {Task : TaskType} {H : TaskCost Task} {Job : JobType} {H1 : JobTask Job Task} 
  {H2 : JobCost Job} {MaxArr : MaxArrivals Task} (tsk : Equality.sort Task) (arr_seq : arrival_sequence Job),
@jobs_have_valid_job_costs Task H Job H1 H2 ->
@respects_max_arrivals Task Job H1 arr_seq tsk (MaxArr tsk) ->
@respects_max_request_bound Task Job H1 H2 arr_seq tsk (@task_max_rbf Task H MaxArr tsk)

respects_arrival_curve_to_max_rbf is not universe polymorphic
Arguments respects_arrival_curve_to_max_rbf {Task H Job H1 H2 MaxArr} tsk arr_seq _ _ t1 t2 _
respects_arrival_curve_to_max_rbf is opaque
Expands to: Constant prosa.model.task.arrival.curve_as_rbf.respects_arrival_curve_to_max_rbf
Declared in library prosa.model.task.arrival.curve_as_rbf, line 82, characters 12-45
@respects_arrival_curve_to_max_rbf
     : forall (Task : TaskType) (H : TaskCost Task) (Job : JobType) (H1 : JobTask Job Task)
         (H2 : JobCost Job) (MaxArr : MaxArrivals Task) (tsk : Equality.sort Task)
         (arr_seq : arrival_sequence Job),
       @jobs_have_valid_job_costs Task H Job H1 H2 ->
       @respects_max_arrivals Task Job H1 arr_seq tsk (MaxArr tsk) ->
       @respects_max_request_bound Task Job H1 H2 arr_seq tsk (@task_max_rbf Task H MaxArr tsk)
```

## Lean

```lean
@Prosa.Model.Task.Arrival.CurveAsRbf.respects_arrival_curve_to_max_rbf : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobCost Job] [MaxArr : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] (tsk : Task)
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Model.Task.Concept.jobs_have_valid_job_costs →
    Prosa.Model.Task.Arrival.Curves.respects_max_arrivals arr_seq tsk
        (Prosa.Model.Task.Arrival.Curves.max_arrivals tsk) →
      Prosa.Model.Task.Arrival.RequestBoundFunctions.respects_max_request_bound arr_seq tsk
        (Prosa.Model.Task.Arrival.CurveAsRbf.task_max_rbf Prosa.Model.Task.Arrival.Curves.max_arrivals tsk)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_CurveAsRbf_respects_arrival_curve_to_max_rbf
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job)
         (inst_13 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_10 Task
            inst_3)
         (inst_17 : 
          Prosa_Behavior_Job_JobCost Job
            inst_10)
         (MaxArr : Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
                     inst_3)
         (tsk : Task)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_10),
       Prosa_Model_Task_Concept_jobs_have_valid_job_costs Task
         inst_3
         inst_6 Job
         inst_10
         inst_13
         inst_17 ->
       Prosa_Model_Task_Arrival_Curves_respects_max_arrivals Task
         inst_3 Job
         inst_10
         inst_13 arr_seq tsk
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3 MaxArr tsk) ->
       Prosa_Model_Task_Arrival_RequestBoundFunctions_respects_max_request_bound Task
         inst_3 Job
         inst_10
         inst_13
         inst_17 arr_seq tsk
         (Prosa_Model_Task_Arrival_CurveAsRbf_task_max_rbf Task
            inst_3
            inst_6
            (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
               inst_3 MaxArr)
            tsk)
```
