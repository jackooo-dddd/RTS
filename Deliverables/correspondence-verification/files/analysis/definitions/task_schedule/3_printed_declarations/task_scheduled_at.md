# `task_scheduled_at`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.task_schedule.task_scheduled_at`
- Lean: `Prosa.Analysis.Definitions.TaskSchedule.task_scheduled_at`
- Certificate: `task_scheduled_at_correspondence`

## Official Rocq

```coq
task_scheduled_at :
forall {Task : TaskType} {Job : JobType},
JobTask Job Task ->
arrival_sequence Job ->
forall {PState : ProcessorState Job}, @schedule Job PState -> Equality.sort Task -> instant -> bool

task_scheduled_at is not universe polymorphic
Arguments task_scheduled_at {Task Job H0} arr_seq {PState} sched tsk t
task_scheduled_at is transparent
Expands to: Constant prosa.analysis.definitions.task_schedule.task_scheduled_at
Declared in library prosa.analysis.definitions.task_schedule, line 36, characters 13-30
@task_scheduled_at
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task ->
       arrival_sequence Job ->
       forall PState : ProcessorState Job, @schedule Job PState -> Equality.sort Task -> instant -> bool
```

Body:

```coq
task_scheduled_at =
fun (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (arr_seq : arrival_sequence Job)
  (PState : ProcessorState Job) (sched : @schedule Job PState) (tsk : Equality.sort Task) 
  (t : instant) =>
@scheduled_jobs_of_task_at Task Job H0 arr_seq PState sched tsk t != [::]
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task ->
       arrival_sequence Job ->
       forall {PState : ProcessorState Job}, @schedule Job PState -> Equality.sort Task -> instant -> bool

Arguments task_scheduled_at {Task Job H0} arr_seq {PState} sched tsk t
```

## Lean

```lean
@Prosa.Analysis.Definitions.TaskSchedule.task_scheduled_at : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Prosa.Behavior.Schedule.schedule PState → Task → Prosa.Behavior.Time.instant → Bool
def Prosa.Analysis.Definitions.TaskSchedule.task_scheduled_at.{u_1, u_2, u_3, u_4} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Prosa.Behavior.Schedule.schedule PState → Task → Prosa.Behavior.Time.instant → Bool :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task] {PState} arr_seq sched
    tsk t =>
  !(Prosa.Analysis.Definitions.TaskSchedule.scheduled_jobs_of_task_at arr_seq sched tsk t).isEmpty
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_TaskSchedule_task_scheduled_at
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
       Task -> Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Analysis_Definitions_TaskSchedule_task_scheduled_at@{u_1 u_2 u_3 u_4 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.max__u_2+1_u_3+2_u_4+2.0 Lean.u_3+1.0 Lean.u_4+1.0 Lean.u_1+2.0
Lean.u_2+2.0 Lean.u_4+2.0} =
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
Bool_not
  (List_isEmpty Job
     (Prosa_Analysis_Definitions_TaskSchedule_scheduled_jobs_of_task_at Task
        inst_3 Job
        inst_7
        inst_10 PState arr_seq sched
        tsk t))
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
       Task -> Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Analysis_Definitions_TaskSchedule_task_scheduled_at Task
  inst_3 Job
  inst_7
  inst_10 PState 
  arr_seq sched tsk t
```
