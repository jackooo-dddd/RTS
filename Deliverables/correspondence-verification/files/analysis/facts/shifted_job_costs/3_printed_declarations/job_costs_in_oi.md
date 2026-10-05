# `job_costs_in_oi`

- Kind (Rocq): Instance
- Rocq: `prosa.analysis.facts.shifted_job_costs.job_costs_in_oi`
- Lean: `Prosa.Analysis.Facts.ShiftedJobCosts.job_costs_in_oi`
- Certificate: `job_costs_in_oi_correspondence`

## Official Rocq

```coq
job_costs_in_oi :
forall {Task : TaskType},
TaskOffset Task ->
PeriodicModel Task ->
forall {Job : JobType},
JobTask Job Task ->
JobArrival Job ->
JobCost Job -> arrival_sequence Job -> TaskSet (Equality.sort Task) -> Equality.sort Job -> JobCost Job

job_costs_in_oi is not universe polymorphic
Arguments job_costs_in_oi {Task H H0 Job H2 H3 H4} arr_seq ts j _
job_costs_in_oi is transparent
Expands to: Constant prosa.analysis.facts.shifted_job_costs.job_costs_in_oi
Declared in library prosa.analysis.facts.shifted_job_costs, line 64, characters 2-66
@job_costs_in_oi
     : forall Task : TaskType,
       TaskOffset Task ->
       PeriodicModel Task ->
       forall Job : JobType,
       JobTask Job Task ->
       JobArrival Job ->
       JobCost Job ->
       arrival_sequence Job -> TaskSet (Equality.sort Task) -> Equality.sort Job -> JobCost Job
```

Body:

```coq
job_costs_in_oi =
fun (Task : TaskType) (H : TaskOffset Task) (H0 : PeriodicModel Task) (Job : JobType) 
  (H2 : JobTask Job Task) (H3 : JobArrival Job) (H4 : JobCost Job) (arr_seq : arrival_sequence Job)
  (ts : TaskSet (Equality.sort Task)) (j : Equality.sort Job) =>
let O_max := @max_task_offset Task H ts in
let HP := @hyperperiod Task H0 ts in @job_costs_shifted Task H H0 Job H2 H3 H4 arr_seq ts j
     : forall {Task : TaskType},
       TaskOffset Task ->
       PeriodicModel Task ->
       forall {Job : JobType},
       JobTask Job Task ->
       JobArrival Job ->
       JobCost Job ->
       arrival_sequence Job -> TaskSet (Equality.sort Task) -> Equality.sort Job -> JobCost Job

Arguments job_costs_in_oi {Task H H0 Job H2 H3 H4} arr_seq ts j _
```

## Lean

```lean
@Prosa.Analysis.Facts.ShiftedJobCosts.job_costs_in_oi : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Offset.TaskOffset Task] →
      [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] →
        {Job : Prosa.Behavior.Job.JobType} →
          [inst_3 : DecidableEq Job] →
            [Prosa.Model.Task.Concept.JobTask Job Task] →
              [Prosa.Behavior.Job.JobArrival Job] →
                [Prosa.Behavior.Job.JobCost Job] →
                  Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                    Prosa.Model.Task.Concept.TaskSet Task → Job → Prosa.Behavior.Job.JobCost Job
```

Body:

```lean
@[reducible] def Prosa.Analysis.Facts.ShiftedJobCosts.job_costs_in_oi.{u_1, u_2} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Offset.TaskOffset Task] →
      [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] →
        {Job : Prosa.Behavior.Job.JobType} →
          [inst_3 : DecidableEq Job] →
            [Prosa.Model.Task.Concept.JobTask Job Task] →
              [Prosa.Behavior.Job.JobArrival Job] →
                [Prosa.Behavior.Job.JobCost Job] →
                  Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                    Prosa.Model.Task.Concept.TaskSet Task → Job → Prosa.Behavior.Job.JobCost Job :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Offset.TaskOffset Task]
    [Prosa.Model.Task.Arrival.Periodic.PeriodicModel Task] {Job} [DecidableEq Job]
    [Prosa.Model.Task.Concept.JobTask Job Task] [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobCost Job]
    arr_seq ts j =>
  { job_cost := Prosa.Analysis.Facts.ShiftedJobCosts.job_costs_shifted arr_seq ts j }
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_ShiftedJobCosts_job_costs_in_oi
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Offset_TaskOffset Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_13 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_13 Task
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_13 ->
       Prosa_Behavior_Job_JobCost Job
         inst_13 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_13 ->
       Prosa_Model_Task_Concept_TaskSet Task ->
       Job ->
       Prosa_Behavior_Job_JobCost Job
         inst_13
```

Body:

```coq
Prosa_Analysis_Facts_ShiftedJobCosts_job_costs_in_oi@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
Lean.u_2+1.0 Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Task_Offset_TaskOffset
                                                                                Task
                                                                                inst_3)
  (inst_9 : Prosa_Model_Task_Arrival_Periodic_PeriodicModel
                                                                                Task
                                                                                inst_3)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_13 : DecidableEq Job)
  (inst_16 : Prosa_Model_Task_Concept_JobTask
                                                                                Job
                                                                                inst_13
                                                                                Task
                                                                                inst_3)
  (inst_20 : Prosa_Behavior_Job_JobArrival
                                                                                Job
                                                                                inst_13)
  (inst_23 : Prosa_Behavior_Job_JobCost
                                                                                Job
                                                                                inst_13)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_13)
  (ts : Prosa_Model_Task_Concept_TaskSet Task) (j : Job) =>
Prosa_Behavior_Job_JobCost_mk Job inst_13
  (Prosa_Analysis_Facts_ShiftedJobCosts_job_costs_shifted Task
     inst_3
     inst_6
     inst_9 Job
     inst_13
     inst_16
     inst_20
     inst_23 arr_seq ts j)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Offset_TaskOffset Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Periodic_PeriodicModel Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_13 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_13 Task
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_13 ->
       Prosa_Behavior_Job_JobCost Job
         inst_13 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_13 ->
       Prosa_Model_Task_Concept_TaskSet Task ->
       Job ->
       Prosa_Behavior_Job_JobCost Job
         inst_13

Arguments Prosa_Analysis_Facts_ShiftedJobCosts_job_costs_in_oi Task
  inst_3
  inst_6
  inst_9 Job
  inst_13
  inst_16
  inst_20
  inst_23 arr_seq 
  ts j
```
