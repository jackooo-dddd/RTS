# `task_service_at`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.task_schedule.task_service_at`
- Lean: `Prosa.Analysis.Definitions.TaskSchedule.task_service_at`
- Certificate: `task_service_at_correspondence`

## Official Rocq

```coq
task_service_at :
forall {Task : TaskType} {Job : JobType},
JobTask Job Task ->
arrival_sequence Job ->
forall {PState : ProcessorState Job}, @schedule Job PState -> Equality.sort Task -> instant -> nat

task_service_at is not universe polymorphic
Arguments task_service_at {Task Job H0} arr_seq {PState} sched tsk t
task_service_at is transparent
Expands to: Constant prosa.analysis.definitions.task_schedule.task_service_at
Declared in library prosa.analysis.definitions.task_schedule, line 42, characters 13-28
@task_service_at
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task ->
       arrival_sequence Job ->
       forall PState : ProcessorState Job, @schedule Job PState -> Equality.sort Task -> instant -> nat
```

Body:

```coq
task_service_at =
fun (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (arr_seq : arrival_sequence Job)
  (PState : ProcessorState Job) (sched : @schedule Job PState) (tsk : Equality.sort Task) 
  (t : instant) =>
\sum_(j <- @scheduled_jobs_of_task_at Task Job H0 arr_seq PState sched tsk t)
   @service_at Job PState sched j t
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task ->
       arrival_sequence Job ->
       forall {PState : ProcessorState Job}, @schedule Job PState -> Equality.sort Task -> instant -> nat

Arguments task_service_at {Task Job H0} arr_seq {PState} sched tsk t
```

## Lean

```lean
@Prosa.Analysis.Definitions.TaskSchedule.task_service_at : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Prosa.Behavior.Schedule.schedule PState → Task → Prosa.Behavior.Time.instant → Prosa.Behavior.Job.work
def Prosa.Analysis.Definitions.TaskSchedule.task_service_at.{u_1, u_2, u_3, u_4} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Prosa.Behavior.Schedule.schedule PState → Task → Prosa.Behavior.Time.instant → Prosa.Behavior.Job.work :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task] {PState} arr_seq sched
    tsk t =>
  List.foldr (fun j total => Prosa.Behavior.Service.service_at sched j t + total) 0
    (Prosa.Analysis.Definitions.TaskSchedule.scheduled_jobs_of_task_at arr_seq sched tsk t)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_TaskSchedule_task_service_at
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
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_7 PState ->
       Task -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Job_work
```

Body:

```coq
Prosa_Analysis_Definitions_TaskSchedule_task_service_at@{u_1 u_2 u_3 u_4 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
Lean.u_2+1.0 Lean.max__u_2+1_u_3+2_u_4+2.0 Lean.u_3+1.0 Lean.u_4+1.0 Lean.u_1+2.0 Lean.u_2+2.0
Lean.u_4+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (Job : Prosa_Behavior_Job_JobType)
  (inst_7 : DecidableEq Job)
  (inst_10 : 
   Prosa_Model_Task_Concept_JobTask Job
     inst_7 Task
     inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_7)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_7)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_7 PState)
  (tsk : Task) (t : Prosa_Behavior_Time_instant) =>
List_foldr_inst2 Job Prosa_Behavior_Job_work
  (fun (j : Job) (total : Prosa_Behavior_Job_work) =>
   HAdd_hAdd_inst7 Prosa_Behavior_Job_work Prosa_Behavior_Job_work Prosa_Behavior_Job_work
     (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
     (Prosa_Behavior_Service_service_at Job
        inst_7 PState sched j t)
     total)
  (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
  (Prosa_Analysis_Definitions_TaskSchedule_scheduled_jobs_of_task_at Task
     inst_3 Job
     inst_7
     inst_10 PState arr_seq sched tsk t)
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
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_7 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_7 PState ->
       Task -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Job_work

Arguments Prosa_Analysis_Definitions_TaskSchedule_task_service_at Task
  inst_3 Job
  inst_7
  inst_10 PState 
  arr_seq sched tsk t
```
