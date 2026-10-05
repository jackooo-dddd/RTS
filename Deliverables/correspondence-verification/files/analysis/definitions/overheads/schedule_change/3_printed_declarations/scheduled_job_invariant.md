# `scheduled_job_invariant`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.overheads.schedule_change.scheduled_job_invariant`
- Lean: `Prosa.Analysis.Definitions.Overheads.ScheduleChange.scheduled_job_invariant`
- Certificate: `scheduled_job_invariant_correspondence`

## Official Rocq

```coq
scheduled_job_invariant :
forall {Job : JobType},
@schedule Job (processor_state Job) -> option (Equality.sort Job) -> instant -> instant -> bool

scheduled_job_invariant is not universe polymorphic
Arguments scheduled_job_invariant {Job} sched oj t1 t2
scheduled_job_invariant is transparent
Expands to: Constant prosa.analysis.definitions.overheads.schedule_change.scheduled_job_invariant
Declared in library prosa.analysis.definitions.overheads.schedule_change, line 42, characters 13-36
@scheduled_job_invariant
     : forall Job : JobType,
       @schedule Job (processor_state Job) -> option (Equality.sort Job) -> instant -> instant -> bool
```

Body:

```coq
scheduled_job_invariant =
fun (Job : JobType) (sched : @schedule Job (processor_state Job)) (oj : option (Equality.sort Job))
  (t1 t2 : instant) =>
@all instant (fun t : instant => @scheduled_job Job sched t == oj) (index_iota t1 t2)
     : forall {Job : JobType},
       @schedule Job (processor_state Job) -> option (Equality.sort Job) -> instant -> instant -> bool

Arguments scheduled_job_invariant {Job} sched oj t1 t2
```

## Lean

```lean
@Prosa.Analysis.Definitions.Overheads.ScheduleChange.scheduled_job_invariant : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job) →
      Option Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → Bool
def Prosa.Analysis.Definitions.Overheads.ScheduleChange.scheduled_job_invariant.{u_1} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job) →
      Option Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] sched oj t1 t2 =>
  (Prosa.Util.List.index_iota t1 t2).all fun t => decide (Prosa.Model.Processor.Overheads.scheduled_job sched t = oj)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Overheads_ScheduleChange_scheduled_job_invariant
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3) ->
       Option Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Analysis_Definitions_Overheads_ScheduleChange_scheduled_job_invariant@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
             inst_3
             (Prosa_Model_Processor_Overheads_processor_state Job
                inst_3))
  (oj : Option Job) (t1 t2 : Prosa_Behavior_Time_instant) =>
List_all_inst1 Nat (Prosa_Util_List_index_iota t1 t2)
  (fun t : Nat =>
   Decidable_decide
     (@eq (Option Job)
        (Prosa_Model_Processor_Overheads_scheduled_job Job
           inst_3 sched t)
        oj)
     (Option_instDecidableEq Job
        inst_3
        (Prosa_Model_Processor_Overheads_scheduled_job Job
           inst_3 sched t)
        oj))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3) ->
       Option Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Analysis_Definitions_Overheads_ScheduleChange_scheduled_job_invariant 
  Job inst_3 
  sched oj t1 t
```
