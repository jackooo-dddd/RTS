# `schedule_change`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.overheads.schedule_change.schedule_change`
- Lean: `Prosa.Analysis.Definitions.Overheads.ScheduleChange.schedule_change`
- Certificate: `schedule_change_correspondence`

## Official Rocq

```coq
schedule_change : forall {Job : JobType}, @schedule Job (processor_state Job) -> instant -> bool

schedule_change is not universe polymorphic
Arguments schedule_change {Job} sched t
schedule_change is transparent
Expands to: Constant prosa.analysis.definitions.overheads.schedule_change.schedule_change
Declared in library prosa.analysis.definitions.overheads.schedule_change, line 19, characters 13-28
@schedule_change
     : forall Job : JobType, @schedule Job (processor_state Job) -> instant -> bool
```

Body:

```coq
schedule_change =
fun (Job : JobType) (sched : @schedule Job (processor_state Job)) (t : instant) =>
@scheduled_job Job sched t.-1 != @scheduled_job Job sched t
     : forall {Job : JobType}, @schedule Job (processor_state Job) -> instant -> bool

Arguments schedule_change {Job} sched t
```

## Lean

```lean
@Prosa.Analysis.Definitions.Overheads.ScheduleChange.schedule_change : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job) →
      Prosa.Behavior.Time.instant → Bool
def Prosa.Analysis.Definitions.Overheads.ScheduleChange.schedule_change.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job) →
      Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] sched t =>
  decide
    (Prosa.Model.Processor.Overheads.scheduled_job sched (Nat.pred t) ≠
      Prosa.Model.Processor.Overheads.scheduled_job sched t)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Overheads_ScheduleChange_schedule_change
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3) ->
       Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Analysis_Definitions_Overheads_ScheduleChange_schedule_change@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : 
   DecidableEq Job)
  (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
             inst_3
             (Prosa_Model_Processor_Overheads_processor_state Job
                inst_3))
  (t : Prosa_Behavior_Time_instant) =>
Decidable_decide
  (Ne (Option Job)
     (Prosa_Model_Processor_Overheads_scheduled_job Job
        inst_3 sched
        (Nat_pred t))
     (Prosa_Model_Processor_Overheads_scheduled_job Job
        inst_3 sched t))
  (instDecidableNot
     (@eq (Option Job)
        (Prosa_Model_Processor_Overheads_scheduled_job Job
           inst_3 sched
           (Nat_pred t))
        (Prosa_Model_Processor_Overheads_scheduled_job Job
           inst_3 sched t))
     (Option_instDecidableEq Job
        inst_3
        (Prosa_Model_Processor_Overheads_scheduled_job Job
           inst_3 sched
           (Nat_pred t))
        (Prosa_Model_Processor_Overheads_scheduled_job Job
           inst_3 sched t)))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3) ->
       Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Analysis_Definitions_Overheads_ScheduleChange_schedule_change Job
  inst_3 
  sched t
```
