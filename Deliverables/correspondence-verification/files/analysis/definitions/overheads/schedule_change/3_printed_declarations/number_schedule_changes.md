# `number_schedule_changes`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.overheads.schedule_change.number_schedule_changes`
- Lean: `Prosa.Analysis.Definitions.Overheads.ScheduleChange.number_schedule_changes`
- Certificate: `number_schedule_changes_correspondence`

## Official Rocq

```coq
number_schedule_changes :
forall {Job : JobType}, @schedule Job (processor_state Job) -> instant -> instant -> nat

number_schedule_changes is not universe polymorphic
Arguments number_schedule_changes {Job} sched t1 t2
number_schedule_changes is transparent
Expands to: Constant prosa.analysis.definitions.overheads.schedule_change.number_schedule_changes
Declared in library prosa.analysis.definitions.overheads.schedule_change, line 24, characters 13-36
@number_schedule_changes
     : forall Job : JobType, @schedule Job (processor_state Job) -> instant -> instant -> nat
```

Body:

```coq
number_schedule_changes =
fun (Job : JobType) (sched : @schedule Job (processor_state Job)) (t1 t2 : instant) =>
@count instant (@schedule_change Job sched) (index_iota t1 t2)
     : forall {Job : JobType}, @schedule Job (processor_state Job) -> instant -> instant -> nat

Arguments number_schedule_changes {Job} sched t1 t2
```

## Lean

```lean
@Prosa.Analysis.Definitions.Overheads.ScheduleChange.number_schedule_changes : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job) →
      Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ
def Prosa.Analysis.Definitions.Overheads.ScheduleChange.number_schedule_changes.{u_1} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job) →
      Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ :=
fun {Job} [DecidableEq Job] sched t1 t2 =>
  List.countP (Prosa.Analysis.Definitions.Overheads.ScheduleChange.schedule_change sched)
    (Prosa.Util.List.index_iota t1 t2)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Overheads_ScheduleChange_number_schedule_changes
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3) ->
       Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat
```

Body:

```coq
Prosa_Analysis_Definitions_Overheads_ScheduleChange_number_schedule_changes@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : 
   DecidableEq Job)
  (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
             inst_3
             (Prosa_Model_Processor_Overheads_processor_state Job
                inst_3))
  (t1 t2 : Prosa_Behavior_Time_instant) =>
List_countP_inst1 Prosa_Behavior_Time_instant
  (Prosa_Analysis_Definitions_Overheads_ScheduleChange_schedule_change Job
     inst_3 sched)
  (Prosa_Util_List_index_iota t1 t2)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3) ->
       Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat

Arguments Prosa_Analysis_Definitions_Overheads_ScheduleChange_number_schedule_changes 
  Job inst_3 
  sched t1 t2
```
