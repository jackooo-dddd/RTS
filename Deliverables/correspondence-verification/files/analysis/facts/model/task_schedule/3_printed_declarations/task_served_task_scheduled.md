# `task_served_task_scheduled`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.task_schedule.task_served_task_scheduled`
- Lean: `Prosa.Analysis.Facts.Model.TaskSchedule.task_served_task_scheduled`
- Certificate: `task_served_task_scheduled_correspondence`

## Official Rocq

```coq
task_served_task_scheduled :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} (arr_seq : arrival_sequence Job)
  {PState : ProcessorState Job} (sched : @schedule Job PState) (tsk : Equality.sort Task) 
  (t : instant),
is_true (@task_served_at Task Job H0 arr_seq PState sched tsk t) ->
is_true (@task_scheduled_at Task Job H0 arr_seq PState sched tsk t)

task_served_task_scheduled is not universe polymorphic
Arguments task_served_task_scheduled {Task Job H0} arr_seq {PState} sched tsk t _
task_served_task_scheduled is opaque
Expands to: Constant prosa.analysis.facts.model.task_schedule.task_served_task_scheduled
Declared in library prosa.analysis.facts.model.task_schedule, line 42, characters 8-34
@task_served_task_scheduled
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (arr_seq : arrival_sequence Job)
         (PState : ProcessorState Job) (sched : @schedule Job PState) (tsk : Equality.sort Task)
         (t : instant),
       is_true (@task_served_at Task Job H0 arr_seq PState sched tsk t) ->
       is_true (@task_scheduled_at Task Job H0 arr_seq PState sched tsk t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.TaskSchedule.task_served_task_scheduled : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState) (tsk : Task)
  (t : Prosa.Behavior.Time.instant),
  Prosa.Analysis.Definitions.TaskSchedule.task_served_at arr_seq sched tsk t = true →
    Prosa.Analysis.Definitions.TaskSchedule.task_scheduled_at arr_seq sched tsk t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_TaskSchedule_task_served_task_scheduled
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_7 PState)
         (tsk : Task) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Analysis_Definitions_TaskSchedule_task_served_at Task
            inst_3 Job
            inst_7
            inst_10 PState arr_seq
            sched tsk t)
         Bool_true ->
       @eq Bool
         (Prosa_Analysis_Definitions_TaskSchedule_task_scheduled_at Task
            inst_3 Job
            inst_7
            inst_10 PState arr_seq
            sched tsk t)
         Bool_true
```
