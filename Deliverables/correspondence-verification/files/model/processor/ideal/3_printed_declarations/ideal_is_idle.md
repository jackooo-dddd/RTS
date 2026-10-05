# `ideal_is_idle`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.ideal.ideal_is_idle`
- Lean: `Prosa.Model.Processor.Ideal.ideal_is_idle`
- Certificate: `ideal_is_idle_correspondence`

## Official Rocq

```coq
ideal_is_idle : forall {Job : JobType}, @schedule Job (processor_state Job) -> instant -> bool

ideal_is_idle is not universe polymorphic
Arguments ideal_is_idle {Job} sched t
ideal_is_idle is transparent
Expands to: Constant prosa.model.processor.ideal.ideal_is_idle
Declared in library prosa.model.processor.ideal, line 64, characters 13-26
@ideal_is_idle
     : forall Job : JobType, @schedule Job (processor_state Job) -> instant -> bool
```

Body:

```coq
ideal_is_idle =
fun (Job : JobType) (sched : @schedule Job (processor_state Job)) (t : instant) =>
sched t == @None (Equality.sort Job)
     : forall {Job : JobType}, @schedule Job (processor_state Job) -> instant -> bool

Arguments ideal_is_idle {Job} sched t
```

## Lean

```lean
@Prosa.Model.Processor.Ideal.ideal_is_idle : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
      Prosa.Behavior.Time.instant → Bool
def Prosa.Model.Processor.Ideal.ideal_is_idle.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job) →
      Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] sched t =>
  match sched t with
  | none => true
  | some val => false
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_Ideal_ideal_is_idle
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3) ->
       Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Model_Processor_Ideal_ideal_is_idle@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
             inst_3
             (Prosa_Model_Processor_Ideal_processor_state Job
                inst_3))
  (t : Prosa_Behavior_Time_instant) =>
Prosa_Model_Processor_Ideal_ideal_is_idle_match_1 Job
  inst_3
  (fun
     _ : Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
           inst_3
           (Prosa_Model_Processor_Ideal_processor_state Job
              inst_3) =>
   Bool)
  (sched t) (fun _ : Unit => Bool_true) (fun _ : Job => Bool_false)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3) ->
       Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Model_Processor_Ideal_ideal_is_idle Job
  inst_3 sched t
```
