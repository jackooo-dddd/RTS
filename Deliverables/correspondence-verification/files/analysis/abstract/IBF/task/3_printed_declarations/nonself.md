# `nonself`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.abstract.IBF.task.nonself`
- Lean: `Prosa.Analysis.Abstract.IBF.Task.nonself`
- Certificate: `nonself_correspondence`

## Official Rocq

```coq
nonself :
forall {Job : JobType} {Task : TaskType},
JobTask Job Task ->
forall {PState : ProcessorState Job},
arrival_sequence Job -> @schedule Job PState -> Equality.sort Job -> instant -> bool

nonself is not universe polymorphic
Arguments nonself {Job Task H PState} arr_seq sched j t
nonself is transparent
Expands to: Constant prosa.analysis.abstract.IBF.task.nonself
Declared in library prosa.analysis.abstract.IBF.task, line 50, characters 13-20
@nonself
     : forall (Job : JobType) (Task : TaskType),
       JobTask Job Task ->
       forall PState : ProcessorState Job,
       arrival_sequence Job -> @schedule Job PState -> Equality.sort Job -> instant -> bool
```

Body:

```coq
nonself =
fun (Job : JobType) (Task : TaskType) (H : JobTask Job Task) (PState : ProcessorState Job)
  (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) (j : Equality.sort Job) 
  (t : instant) =>
~~ @task_served_at Task Job H arr_seq PState sched (@job_task Job Task H j) t
     : forall {Job : JobType} {Task : TaskType},
       JobTask Job Task ->
       forall {PState : ProcessorState Job},
       arrival_sequence Job -> @schedule Job PState -> Equality.sort Job -> instant -> bool

Arguments nonself {Job Task H PState} arr_seq sched j t
```

## Lean

```lean
@Prosa.Analysis.Abstract.IBF.Task.nonself : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Prosa.Behavior.Schedule.schedule PState → Job → Prosa.Behavior.Time.instant → Bool
```

Body:

```lean
def Prosa.Analysis.Abstract.IBF.Task.nonself.{u_1, u_2, u_3, u_4} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {Task : Prosa.Model.Task.Concept.TaskType} →
      [inst_1 : DecidableEq Task] →
        [Prosa.Model.Task.Concept.JobTask Job Task] →
          {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job →
              Prosa.Behavior.Schedule.schedule PState → Job → Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] {Task} [DecidableEq Task] [Prosa.Model.Task.Concept.JobTask Job Task] {PState} arr_seq sched
    j t =>
  !Prosa.Analysis.Definitions.TaskSchedule.task_served_at arr_seq sched (Prosa.Model.Task.Concept.job_task j) t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_IBF_Task_nonself
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job
         inst_3 Task
         inst_7 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job -> Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Analysis_Abstract_IBF_Task_nonself@{u_1 u_2 u_3 u_4 Lean.u_1+1.0 Lean.max__u_1+1_u_2+1.0
Lean.max__u_1+1_u_3+2_u_4+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_4+1.0 Lean.u_1+2.0 Lean.u_2+2.0
Lean.u_4+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_7 : DecidableEq Task)
  (inst_10 : Prosa_Model_Task_Concept_JobTask
                                                                              Job
                                                                              inst_3
                                                                              Task
                                                                              inst_7)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (j : Job) (t : Prosa_Behavior_Time_instant) =>
Bool_not
  (Prosa_Analysis_Definitions_TaskSchedule_task_served_at Task
     inst_7 Job
     inst_3
     inst_10 PState arr_seq sched
     (Prosa_Model_Task_Concept_JobTask_job_task Job
        inst_3 Task
        inst_7
        inst_10 j)
     t)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task),
       Prosa_Model_Task_Concept_JobTask Job
         inst_3 Task
         inst_7 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job -> Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Analysis_Abstract_IBF_Task_nonself Job
  inst_3 Task
  inst_7
  inst_10 PState arr_seq 
  sched j t
```
