# `no_task_scheduled_when_idle`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.task_schedule.no_task_scheduled_when_idle`
- Lean: `Prosa.Analysis.Facts.Model.TaskSchedule.no_task_scheduled_when_idle`
- Certificate: `no_task_scheduled_when_idle_correspondence`

## Official Rocq

```coq
no_task_scheduled_when_idle :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {H1 : JobArrival Job}
  (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall {PState : ProcessorState Job} (sched : @schedule Job PState),
@jobs_come_from_arrival_sequence Job PState sched arr_seq ->
@jobs_must_arrive_to_execute Job H1 PState sched ->
forall (tsk : Equality.sort Task) (t : instant),
is_true (@is_idle Job PState arr_seq sched t) ->
is_true (~~ @task_scheduled_at Task Job H0 arr_seq PState sched tsk t)

no_task_scheduled_when_idle is not universe polymorphic
Arguments no_task_scheduled_when_idle {Task Job H0 H1} arr_seq H_valid_arrivals {PState} 
  sched H_jobs_come_from_arrival_sequence H_jobs_must_arrive_to_execute tsk t _
no_task_scheduled_when_idle is opaque
Expands to: Constant prosa.analysis.facts.model.task_schedule.no_task_scheduled_when_idle
Declared in library prosa.analysis.facts.model.task_schedule, line 67, characters 8-35
@no_task_scheduled_when_idle
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H1 : JobArrival Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall (PState : ProcessorState Job) (sched : @schedule Job PState),
       @jobs_come_from_arrival_sequence Job PState sched arr_seq ->
       @jobs_must_arrive_to_execute Job H1 PState sched ->
       forall (tsk : Equality.sort Task) (t : instant),
       is_true (@is_idle Job PState arr_seq sched t) ->
       is_true (~~ @task_scheduled_at Task Job H0 arr_seq PState sched tsk t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.TaskSchedule.no_task_scheduled_when_idle : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (PState : Prosa.Behavior.Schedule.ProcessorState Job) (sched : Prosa.Behavior.Schedule.schedule PState),
      Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
        Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
          ∀ (tsk : Task) (t : Prosa.Behavior.Time.instant),
            Prosa.Model.Schedule.Scheduled.is_idle arr_seq sched t = true →
              (!Prosa.Analysis.Definitions.TaskSchedule.task_scheduled_at arr_seq sched tsk t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_TaskSchedule_no_task_scheduled_when_idle
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_14 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_14 arr_seq ->
       forall
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_7 PState),
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence Job
         inst_7 PState sched arr_seq ->
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_7
         inst_14 PState sched ->
       forall (tsk : Task) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Model_Schedule_Scheduled_is_idle Job
            inst_7 PState arr_seq sched
            t)
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Analysis_Definitions_TaskSchedule_task_scheduled_at Task
               inst_3 Job
               inst_7
               inst_10 PState arr_seq
               sched tsk t))
         Bool_true
```
