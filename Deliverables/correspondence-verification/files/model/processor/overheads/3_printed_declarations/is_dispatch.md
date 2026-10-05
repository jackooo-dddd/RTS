# `is_dispatch`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.overheads.is_dispatch`
- Lean: `Prosa.Model.Processor.Overheads.is_dispatch`
- Certificate: `ovh_is_dispatch_correspondence`

## Official Rocq

```coq
is_dispatch : forall {Job : JobType}, @schedule Job (processor_state Job) -> instant -> bool

is_dispatch is not universe polymorphic
Arguments is_dispatch {Job} sched t
is_dispatch is transparent
Expands to: Constant prosa.model.processor.overheads.is_dispatch
Declared in library prosa.model.processor.overheads, line 124, characters 13-24
@is_dispatch
     : forall Job : JobType, @schedule Job (processor_state Job) -> instant -> bool
```

Body:

```coq
is_dispatch =
fun (Job : JobType) (sched : @schedule Job (processor_state Job)) (t : instant) =>
match sched t with
| @Dispatch _ _ => true
| _ => false
end
     : forall {Job : JobType}, @schedule Job (processor_state Job) -> instant -> bool

Arguments is_dispatch {Job} sched t
```

## Lean

```lean
@Prosa.Model.Processor.Overheads.is_dispatch : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job) →
      Prosa.Behavior.Time.instant → Bool
def Prosa.Model.Processor.Overheads.is_dispatch.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job) →
      Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] sched t =>
  Prosa.Model.Processor.Overheads.proc_state.casesOn (sched t) false (fun x x_1 => false) (fun x => true)
    (fun x => false) fun x => false
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_Overheads_is_dispatch
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3) ->
       Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Model_Processor_Overheads_is_dispatch@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
             inst_3
             (Prosa_Model_Processor_Overheads_processor_state Job
                inst_3))
  (t : Prosa_Behavior_Time_instant) =>
Prosa_Model_Processor_Overheads_proc_state_casesOn Job
  (fun _ : Prosa_Model_Processor_Overheads_proc_state Job => Bool) (sched t) Bool_false
  (fun _ _ : Option Job => Bool_false) (fun _ : Option Job => Bool_true) (fun _ : Job => Bool_false)
  (fun _ : Job => Bool_false)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3) ->
       Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Model_Processor_Overheads_is_dispatch Job
  inst_3 sched t
```
