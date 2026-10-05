# `taskset_respects_arrival_curve_to_max_rbf`

- Kind (Rocq): Corollary
- Rocq: `prosa.model.task.arrival.curve_as_rbf.taskset_respects_arrival_curve_to_max_rbf`
- Lean: `Prosa.Model.Task.Arrival.CurveAsRbf.taskset_respects_arrival_curve_to_max_rbf`
- Certificate: `taskset_respects_arrival_curve_to_max_rbf_correspondence`

## Official Rocq

```coq
taskset_respects_arrival_curve_to_max_rbf :
forall {Task : TaskType} {H : TaskCost Task} {Job : JobType} {H1 : JobTask Job Task} 
  {H2 : JobCost Job} {MaxArr : MaxArrivals Task} (ts : TaskSet (Equality.sort Task))
  (arr_seq : arrival_sequence Job),
@jobs_have_valid_job_costs Task H Job H1 H2 ->
@taskset_respects_max_arrivals Task Job H1 arr_seq MaxArr ts ->
@taskset_respects_max_request_bound Task Job H1 H2 arr_seq (@MaxArrivalsRBF Task H MaxArr) ts

taskset_respects_arrival_curve_to_max_rbf is not universe polymorphic
Arguments taskset_respects_arrival_curve_to_max_rbf {Task H Job H1 H2 MaxArr} ts arr_seq _ _ tsk _ t1 t2 _
taskset_respects_arrival_curve_to_max_rbf is opaque
Expands to: Constant prosa.model.task.arrival.curve_as_rbf.taskset_respects_arrival_curve_to_max_rbf
Declared in library prosa.model.task.arrival.curve_as_rbf, line 150, characters 14-55
@taskset_respects_arrival_curve_to_max_rbf
     : forall (Task : TaskType) (H : TaskCost Task) (Job : JobType) (H1 : JobTask Job Task)
         (H2 : JobCost Job) (MaxArr : MaxArrivals Task) (ts : TaskSet (Equality.sort Task))
         (arr_seq : arrival_sequence Job),
       @jobs_have_valid_job_costs Task H Job H1 H2 ->
       @taskset_respects_max_arrivals Task Job H1 arr_seq MaxArr ts ->
       @taskset_respects_max_request_bound Task Job H1 H2 arr_seq (@MaxArrivalsRBF Task H MaxArr) ts
```

## Lean

```lean
@Prosa.Model.Task.Arrival.CurveAsRbf.taskset_respects_arrival_curve_to_max_rbf : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobCost Job] [MaxArr : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
  (ts : Prosa.Model.Task.Concept.TaskSet Task) (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Model.Task.Concept.jobs_have_valid_job_costs →
    Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
      Prosa.Model.Task.Arrival.RequestBoundFunctions.taskset_respects_max_request_bound arr_seq ts
```

## Lean, imported into Rocq

```coq
Prosa_Model_Task_Arrival_CurveAsRbf_taskset_respects_arrival_curve_to_max_rbf
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
         (ts : Prosa_Model_Task_Concept_TaskSet Task)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_10),
       Prosa_Model_Task_Concept_jobs_have_valid_job_costs Task
         inst_3
         inst_6 Job
         inst_10
         inst_13
         inst_17 ->
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_10
         inst_13 arr_seq MaxArr ts ->
       Prosa_Model_Task_Arrival_RequestBoundFunctions_taskset_respects_max_request_bound Task
         inst_3 Job
         inst_10
         inst_13
         inst_17 arr_seq
         (Prosa_Model_Task_Arrival_CurveAsRbf_MaxArrivalsRBF Task
            inst_3
            inst_6 MaxArr)
         ts
```
