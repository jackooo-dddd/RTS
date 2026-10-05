# `task_service_of_jobs_in`

- Kind (Rocq): Definition
- Rocq: `prosa.model.aggregate.service_of_jobs.task_service_of_jobs_in`
- Lean: `Prosa.Model.Aggregate.ServiceOfJobs.task_service_of_jobs_in`
- Certificate: `task_service_of_jobs_in_correspondence`

## Official Rocq

```coq
task_service_of_jobs_in :
forall {Task : TaskType} {Job : JobType},
JobTask Job Task ->
forall {PState : ProcessorState Job},
@schedule Job PState -> Equality.sort Task -> seq (Equality.sort Job) -> instant -> instant -> nat

task_service_of_jobs_in is not universe polymorphic
Arguments task_service_of_jobs_in {Task Job H PState} sched tsk jobs%seq_scope t1 t2
task_service_of_jobs_in is transparent
Expands to: Constant prosa.model.aggregate.service_of_jobs.task_service_of_jobs_in
Declared in library prosa.model.aggregate.service_of_jobs, line 105, characters 15-38
@task_service_of_jobs_in
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task ->
       forall PState : ProcessorState Job,
       @schedule Job PState -> Equality.sort Task -> seq (Equality.sort Job) -> instant -> instant -> nat
```

Body:

```coq
task_service_of_jobs_in =
fun (Task : TaskType) (Job : JobType) (H : JobTask Job Task) (PState : ProcessorState Job)
  (sched : @schedule Job PState) (tsk : Equality.sort Task) (jobs : seq (Equality.sort Job)) 
  (t1 : instant) =>
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task ->
       forall {PState : ProcessorState Job},
       @schedule Job PState -> Equality.sort Task -> seq (Equality.sort Job) -> instant -> instant -> nat

Arguments task_service_of_jobs_in {Task Job H PState} sched tsk jobs%seq_scope t1 t2
```

## Lean

```lean
@Prosa.Model.Aggregate.ServiceOfJobs.task_service_of_jobs_in : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
            Prosa.Behavior.Schedule.schedule PState →
              Task → List Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ
```

Body:

```lean
def Prosa.Model.Aggregate.ServiceOfJobs.task_service_of_jobs_in.{u_1, u_2, u_3, u_4} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
            Prosa.Behavior.Schedule.schedule PState →
              Task → List Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task] {PState} sched tsk
    jobs t1 t2 =>
  Prosa.Model.Aggregate.ServiceOfJobs.service_of_jobs sched (Prosa.Model.Task.Concept.job_of_task tsk) jobs t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Model_Aggregate_ServiceOfJobs_task_service_of_jobs_in
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_7,
       Prosa_Behavior_Schedule_schedule Job
         inst_7 PState ->
       Task -> List Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat
```

Body:

```coq
Prosa_Model_Aggregate_ServiceOfJobs_task_service_of_jobs_in@{u_1 u_2 u_3 u_4 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.max__u_2+1_u_3+2_u_4+2.0 Lean.u_3+1.0 Lean.u_4+1.0 Lean.u_1+2.0
Lean.u_2+2.0 Lean.u_4+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_7 : DecidableEq Job)
  (inst_10 : Prosa_Model_Task_Concept_JobTask
                                                                                Job
                                                                                inst_7
                                                                                Task
                                                                                inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_7)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_7 PState)
  (tsk : Task) (jobs : List Job) (t1 t2 : Prosa_Behavior_Time_instant) =>
Prosa_Model_Aggregate_ServiceOfJobs_service_of_jobs Job
  inst_7 PState sched
  (Prosa_Model_Task_Concept_job_of_task Job
     inst_7 Task
     inst_3
     inst_10 tsk)
  jobs t1 t2
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job),
       Prosa_Model_Task_Concept_JobTask Job
         inst_7 Task
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_7,
       Prosa_Behavior_Schedule_schedule Job
         inst_7 PState ->
       Task -> List Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat

Arguments Prosa_Model_Aggregate_ServiceOfJobs_task_service_of_jobs_in Task
  inst_3 Job
  inst_7
  inst_10 PState 
  sched tsk jobs t1 t
```
