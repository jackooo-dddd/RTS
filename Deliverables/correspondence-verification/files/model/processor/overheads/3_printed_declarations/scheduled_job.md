# `scheduled_job`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.overheads.scheduled_job`
- Lean: `Prosa.Model.Processor.Overheads.scheduled_job`
- Certificate: `ovh_scheduled_job_correspondence`

## Official Rocq

```coq
scheduled_job :
forall {Job : JobType}, @schedule Job (processor_state Job) -> instant -> option (Equality.sort Job)

scheduled_job is not universe polymorphic
Arguments scheduled_job {Job} sched t
scheduled_job is transparent
Expands to: Constant prosa.model.processor.overheads.scheduled_job
Declared in library prosa.model.processor.overheads, line 99, characters 13-26
@scheduled_job
     : forall Job : JobType, @schedule Job (processor_state Job) -> instant -> option (Equality.sort Job)
```

Body:

```coq
scheduled_job =
fun (Job : JobType) (sched : @schedule Job (processor_state Job)) (t : instant) =>
match sched t with
| @Idle _ => @None (Equality.sort Job)
| @ContextSwitch _ _ oj | @Dispatch _ oj => oj
| @CacheRelatedPreemptionDelay _ oj | @Progress _ oj => @Some (Equality.sort Job) oj
end
     : forall {Job : JobType}, @schedule Job (processor_state Job) -> instant -> option (Equality.sort Job)

Arguments scheduled_job {Job} sched t
```

## Lean

```lean
@Prosa.Model.Processor.Overheads.scheduled_job : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job) →
      Prosa.Behavior.Time.instant → Option Job
def Prosa.Model.Processor.Overheads.scheduled_job.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job) →
      Prosa.Behavior.Time.instant → Option Job :=
fun {Job} [DecidableEq Job] sched t =>
  Prosa.Model.Processor.Overheads.proc_state.casesOn (sched t) none (fun x oj => oj) (fun oj => oj) (fun j => some j)
    fun j => some j
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_Overheads_scheduled_job
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3) ->
       Prosa_Behavior_Time_instant -> Option Job
```

Body:

```coq
Prosa_Model_Processor_Overheads_scheduled_job@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
             inst_3
             (Prosa_Model_Processor_Overheads_processor_state Job
                inst_3))
  (t : Prosa_Behavior_Time_instant) =>
Prosa_Model_Processor_Overheads_proc_state_casesOn Job
  (fun _ : Prosa_Model_Processor_Overheads_proc_state Job => Option Job) (sched t) 
  (Option_none Job) (fun _ oj : Option Job => oj) (fun oj : Option Job => oj)
  (fun j : Job => Option_some Job j) (fun j : Job => Option_some Job j)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3) ->
       Prosa_Behavior_Time_instant -> Option Job

Arguments Prosa_Model_Processor_Overheads_scheduled_job Job
  inst_3 sched t
```
