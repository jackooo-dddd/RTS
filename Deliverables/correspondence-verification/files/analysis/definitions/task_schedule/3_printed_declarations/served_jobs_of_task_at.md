# `served_jobs_of_task_at`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.task_schedule.served_jobs_of_task_at`
- Lean: `Prosa.Analysis.Definitions.TaskSchedule.served_jobs_of_task_at`
- Certificate: `served_jobs_of_task_at_correspondence`

## Official Rocq

```coq
served_jobs_of_task_at :
forall {Task : TaskType} {Job : JobType},
JobTask Job Task ->
arrival_sequence Job ->
forall {PState : ProcessorState Job},
@schedule Job PState -> Equality.sort Task -> instant -> seq (Equality.sort Job)

served_jobs_of_task_at is not universe polymorphic
Arguments served_jobs_of_task_at {Task Job H0} arr_seq {PState} sched tsk t
served_jobs_of_task_at is transparent
Expands to: Constant prosa.analysis.definitions.task_schedule.served_jobs_of_task_at
Declared in library prosa.analysis.definitions.task_schedule, line 56, characters 13-35
@served_jobs_of_task_at
     : forall (Task : TaskType) (Job : JobType),
       JobTask Job Task ->
       arrival_sequence Job ->
       forall PState : ProcessorState Job,
       @schedule Job PState -> Equality.sort Task -> instant -> seq (Equality.sort Job)
```

Body:

```coq
served_jobs_of_task_at =
fun (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (arr_seq : arrival_sequence Job)
  (PState : ProcessorState Job) (sched : @schedule Job PState) (tsk : Equality.sort Task) 
  (t : instant) =>
   | @receives_service_at Job PState sched j t]
     : forall {Task : TaskType} {Job : JobType},
       JobTask Job Task ->
       arrival_sequence Job ->
       forall {PState : ProcessorState Job},
       @schedule Job PState -> Equality.sort Task -> instant -> seq (Equality.sort Job)

Arguments served_jobs_of_task_at {Task Job H0} arr_seq {PState} sched tsk t
```

## Lean

```lean
@Prosa.Analysis.Definitions.TaskSchedule.served_jobs_of_task_at : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Prosa.Behavior.Schedule.schedule PState → Task → Prosa.Behavior.Time.instant → List Job
def Prosa.Analysis.Definitions.TaskSchedule.served_jobs_of_task_at.{u_1, u_2, u_3, u_4} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    {Job : Prosa.Behavior.Job.JobType} →
      [inst_1 : DecidableEq Job] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Prosa.Behavior.Schedule.schedule PState → Task → Prosa.Behavior.Time.instant → List Job :=
fun {Task} [DecidableEq Task] {Job} [DecidableEq Job] [Prosa.Model.Task.Concept.JobTask Job Task] {PState} arr_seq sched
    tsk t =>
  List.filter (fun j => Prosa.Behavior.Service.receives_service_at sched j t)
    (Prosa.Analysis.Definitions.TaskSchedule.scheduled_jobs_of_task_at arr_seq sched tsk t)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_TaskSchedule_served_jobs_of_task_at
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
       Task -> Prosa_Behavior_Time_instant -> List Job
```

Body:

```coq
Prosa_Analysis_Definitions_TaskSchedule_served_jobs_of_task_at@{u_1 u_2 u_3 u_4 Lean.u_1+1.0
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
List_filter Job
  (fun j : Job =>
   Prosa_Behavior_Service_receives_service_at Job
     inst_7 PState sched j t)
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
       Task -> Prosa_Behavior_Time_instant -> List Job

Arguments Prosa_Analysis_Definitions_TaskSchedule_served_jobs_of_task_at Task
  inst_3 Job
  inst_7
  inst_10 PState 
  arr_seq sched tsk t
```
