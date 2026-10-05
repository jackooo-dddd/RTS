# `job_priority_point`

- Kind (Rocq): Definition
- Rocq: `prosa.model.priority.gel.job_priority_point`
- Lean: `Prosa.Model.Priority.Gel.job_priority_point`
- Certificate: `job_priority_point_correspondence`

## Official Rocq

```coq
job_priority_point :
forall {Job : JobType} {Task : TaskType},
JobTask Job Task ->
PriorityPoint Task ->
JobArrival Job ->
Equality.sort Job ->
ssralg.GRing.Nmodule.sort
  (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
     ssrint.ssrint_int__canonical__GRing_PzSemiRing)

job_priority_point is not universe polymorphic
Arguments job_priority_point {Job Task H H0 H1} j
job_priority_point is transparent
Expands to: Constant prosa.model.priority.gel.job_priority_point
Declared in library prosa.model.priority.gel, line 35, characters 13-31
@job_priority_point
     : forall (Job : JobType) (Task : TaskType),
       JobTask Job Task ->
       PriorityPoint Task ->
       JobArrival Job ->
       Equality.sort Job ->
       ssralg.GRing.Nmodule.sort
         (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
            ssrint.ssrint_int__canonical__GRing_PzSemiRing)
```

Body:

```coq
job_priority_point =
fun (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (H0 : PriorityPoint Task) 
  (H1 : JobArrival Job) (j : Equality.sort Job) =>
@ssralg.GRing.add
  (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
     ssrint.ssrint_int__canonical__GRing_PzSemiRing)
  (@ssralg.GRing.natmul
     (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
        ssrint.ssrint_int__canonical__GRing_PzSemiRing)
     (ssralg.GRing.one ssrint.ssrint_int__canonical__GRing_PzSemiRing) (@job_arrival Job H1 j))
  (@task_priority_point Task H0 (@job_task Job Task H j))
     : forall {Job : JobType} {Task : TaskType},
       JobTask Job Task ->
       PriorityPoint Task ->
       JobArrival Job ->
       Equality.sort Job ->
       ssralg.GRing.Nmodule.sort
         (ssralg.GRing.PzSemiRing.Exports.GRing_PzSemiRing__to__GRing_Nmodule
            ssrint.ssrint_int__canonical__GRing_PzSemiRing)

Arguments job_priority_point {Job Task H H0 H1} j
```

## Lean

```lean
@Prosa.Model.Priority.Gel.job_priority_point : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Model.Priority.Gel.PriorityPoint Task] → [Prosa.Behavior.Job.JobArrival Job] → Job → ℤ
```

Body:

```lean
def Prosa.Model.Priority.Gel.job_priority_point.{u_1, u_2} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          [Prosa.Model.Priority.Gel.PriorityPoint Task] → [Prosa.Behavior.Job.JobArrival Job] → Job → ℤ :=
fun {Job} [DecidableEq Job] {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.JobTask Job Task]
    [Prosa.Model.Priority.Gel.PriorityPoint Task] [Prosa.Behavior.Job.JobArrival Job] j =>
  ↑(Prosa.Behavior.Job.job_arrival j) +
    Prosa.Model.Priority.Gel.task_priority_point (Prosa.Model.Task.Concept.job_task j)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Priority_Gel_job_priority_point
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job inst_3
         Task inst_7 ->
       Prosa_Model_Priority_Gel_PriorityPoint Task
         inst_7 ->
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       Job -> Int
```

Body:

```coq
Prosa_Model_Priority_Gel_job_priority_point@{u_1 u_2 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0
Lean.u_1+2.0 Lean.u_2+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_7 : DecidableEq Task)
  (inst_10 : Prosa_Model_Task_Concept_JobTask Job
                                                                      inst_3
                                                                      Task
                                                                      inst_7)
  (inst_14 : Prosa_Model_Priority_Gel_PriorityPoint
                                                                      Task
                                                                      inst_7)
  (inst_17 : Prosa_Behavior_Job_JobArrival Job
                                                                      inst_3)
  (j : Job) =>
HAdd_hAdd_inst7 Int Prosa_Model_Priority_Gel_offset Int (instHAdd_inst1 Int Int_instAdd)
  (Nat_cast_inst1 Int instNatCastInt
     (Prosa_Behavior_Job_JobArrival_job_arrival Job
        inst_3
        inst_17 j))
  (Prosa_Model_Priority_Gel_PriorityPoint_task_priority_point Task
     inst_7
     inst_14
     (Prosa_Model_Task_Concept_JobTask_job_task Job
        inst_3 Task
        inst_7
        inst_10 j))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job inst_3
         Task inst_7 ->
       Prosa_Model_Priority_Gel_PriorityPoint Task
         inst_7 ->
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       Job -> Int

Arguments Prosa_Model_Priority_Gel_job_priority_point Job
  inst_3 Task
  inst_7
  inst_10
  inst_14
  inst_17 j
```
