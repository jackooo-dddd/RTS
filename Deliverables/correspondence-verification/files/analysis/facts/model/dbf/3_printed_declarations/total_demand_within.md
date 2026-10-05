# `total_demand_within`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.facts.model.dbf.total_demand_within`
- Lean: `Prosa.Analysis.Facts.Model.Dbf.total_demand_within`
- Certificate: `total_demand_within_correspondence`

## Official Rocq

```coq
total_demand_within :
forall {Task : TaskType},
TaskDeadline Task ->
forall {Job : JobType},
JobTask Job Task -> JobArrival Job -> arrival_sequence Job -> JobCost Job -> instant -> instant -> nat

total_demand_within is not universe polymorphic
Arguments total_demand_within {Task H Job H0 H1} arr_seq {H3} t1 t2
total_demand_within is transparent
Expands to: Constant prosa.analysis.facts.model.dbf.total_demand_within
Declared in library prosa.analysis.facts.model.dbf, line 113, characters 13-32
@total_demand_within
     : forall Task : TaskType,
       TaskDeadline Task ->
       forall Job : JobType,
       JobTask Job Task -> JobArrival Job -> arrival_sequence Job -> JobCost Job -> instant -> instant -> nat
```

Body:

```coq
total_demand_within =
fun (Task : TaskType) (H : TaskDeadline Task) (Job : JobType) (H0 : JobTask Job Task) 
  (H1 : JobArrival Job) (arr_seq : arrival_sequence Job) (H3 : JobCost Job) (t1 t2 : instant) =>
let causing_demand :=
  fun j : Equality.sort Job => @job_deadline Job (@job_deadline_from_task_deadline Job Task H H1 H0) j <= t2
  in
@workload_of_jobs Job H3 causing_demand (@arrivals_between Job arr_seq t1 t2)
     : forall {Task : TaskType},
       TaskDeadline Task ->
       forall {Job : JobType},
       JobTask Job Task -> JobArrival Job -> arrival_sequence Job -> JobCost Job -> instant -> instant -> nat

Arguments total_demand_within {Task H Job H0 H1} arr_seq {H3} t1 t2
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Dbf.total_demand_within : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskDeadline Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            [Prosa.Behavior.Job.JobArrival Job] →
              Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                [Prosa.Behavior.Job.JobCost Job] → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ
```

Body:

```lean
def Prosa.Analysis.Facts.Model.Dbf.total_demand_within.{u_1, u_2} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Concept.TaskDeadline Task] →
      {Job : Prosa.Behavior.Job.JobType} →
        [inst_2 : DecidableEq Job] →
          [Prosa.Model.Task.Concept.JobTask Job Task] →
            [Prosa.Behavior.Job.JobArrival Job] →
              Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
                [Prosa.Behavior.Job.JobCost Job] → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.TaskDeadline Task] {Job} [DecidableEq Job]
    [Prosa.Model.Task.Concept.JobTask Job Task] [Prosa.Behavior.Job.JobArrival Job] arr_seq
    [Prosa.Behavior.Job.JobCost Job] t1 t2 =>
  have causing_demand := fun j => decide (Prosa.Behavior.Job.job_deadline j ≤ t2);
  Prosa.Model.Aggregate.Workload.workload_of_jobs causing_demand
    (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 t2)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Dbf_total_demand_within
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskDeadline Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_10 Task
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job inst_10 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_10 ->
       Prosa_Behavior_Job_JobCost Job inst_10 ->
       Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat
```

Body:

```coq
Prosa_Analysis_Facts_Model_Dbf_total_demand_within@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0
Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : Prosa_Model_Task_Concept_TaskDeadline
                                                                           Task
                                                                           inst_3)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_10 : DecidableEq Job)
  (inst_13 : Prosa_Model_Task_Concept_JobTask
                                                                            Job
                                                                            inst_10
                                                                            Task
                                                                            inst_3)
  (inst_17 : Prosa_Behavior_Job_JobArrival Job
                                                                            inst_10)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_10)
  (inst_22 : Prosa_Behavior_Job_JobCost Job
                                                                            inst_10)
  (t1 t2 : Prosa_Behavior_Time_instant) =>
let causing_demand :=
  fun j : Job =>
  Decidable_decide
    (LE_le_inst1 Prosa_Behavior_Time_instant instLENat
       (Prosa_Behavior_Job_JobDeadline_job_deadline Job
          inst_10
          (Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline Job Task
             inst_10
             inst_3
             inst_6
             inst_17
             inst_13)
          j)
       t2)
    (Nat_decLe
       (Prosa_Behavior_Job_JobDeadline_job_deadline Job
          inst_10
          (Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline Job Task
             inst_10
             inst_3
             inst_6
             inst_17
             inst_13)
          j)
       t2)
  in
Prosa_Model_Aggregate_Workload_workload_of_jobs Job
  inst_10
  inst_22 causing_demand
  (Prosa_Behavior_Arrival_sequence_arrivals_between Job
     inst_10 arr_seq t1 t2)
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task),
       Prosa_Model_Task_Concept_TaskDeadline Task
         inst_3 ->
       forall (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_10 Task
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job inst_10 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_10 ->
       Prosa_Behavior_Job_JobCost Job inst_10 ->
       Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat

Arguments Prosa_Analysis_Facts_Model_Dbf_total_demand_within Task
  inst_3
  inst_6 Job
  inst_10
  inst_13
  inst_17 arr_seq
  inst_22 t1 t2
```
