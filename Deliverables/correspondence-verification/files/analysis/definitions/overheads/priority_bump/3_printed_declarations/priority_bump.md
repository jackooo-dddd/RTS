# `priority_bump`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.overheads.priority_bump.priority_bump`
- Lean: `Prosa.Analysis.Definitions.Overheads.PriorityBump.priority_bump`
- Certificate: `priority_bump_correspondence`

## Official Rocq

```coq
priority_bump :
forall {Job : JobType}, JLFP_policy Job -> @schedule Job (processor_state Job) -> instant -> bool

priority_bump is not universe polymorphic
Arguments priority_bump {Job JLFP} sched t
priority_bump is transparent
Expands to: Constant prosa.analysis.definitions.overheads.priority_bump.priority_bump
Declared in library prosa.analysis.definitions.overheads.priority_bump, line 20, characters 13-26
@priority_bump
     : forall Job : JobType, JLFP_policy Job -> @schedule Job (processor_state Job) -> instant -> bool
```

Body:

```coq
priority_bump =
fun (Job : JobType) (JLFP : JLFP_policy Job) (sched : @schedule Job (processor_state Job)) (t : instant) =>
match @scheduled_job Job sched t.-1 with
| @Some _ j1 =>
    match @scheduled_job Job sched t with
    | @Some _ j2 => ~~ @hep_job Job JLFP j1 j2
    | @None _ => false
    end
| @None _ => match @scheduled_job Job sched t with
             | @Some _ _ => true
             | @None _ => false
             end
end
     : forall {Job : JobType}, JLFP_policy Job -> @schedule Job (processor_state Job) -> instant -> bool

Arguments priority_bump {Job JLFP} sched t
```

## Lean

```lean
@Prosa.Analysis.Definitions.Overheads.PriorityBump.priority_bump : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job] →
      Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job) →
        Prosa.Behavior.Time.instant → Bool
```

Body:

```lean
def Prosa.Analysis.Definitions.Overheads.PriorityBump.priority_bump.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job] →
      Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job) →
        Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] [Prosa.Model.Priority.Definitions.JLFP_policy Job] sched t =>
  match Prosa.Model.Processor.Overheads.scheduled_job sched (Nat.pred t),
    Prosa.Model.Processor.Overheads.scheduled_job sched t with
  | none, none => false
  | none, some val => true
  | some val, none => false
  | some j1, some j2 => !Prosa.Model.Priority.Definitions.hep_job j1 j2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Overheads_PriorityBump_priority_bump
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3) ->
       Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Analysis_Definitions_Overheads_PriorityBump_priority_bump@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
            inst_3)
  (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
             inst_3
             (Prosa_Model_Processor_Overheads_processor_state Job
                inst_3))
  (t : Prosa_Behavior_Time_instant) =>
Prosa_Analysis_Definitions_Overheads_PriorityBump_priority_bump_match_1 Job (fun _ _ : Option Job => Bool)
  (Prosa_Model_Processor_Overheads_scheduled_job Job
     inst_3 sched
     (Nat_pred t))
  (Prosa_Model_Processor_Overheads_scheduled_job Job
     inst_3 sched t)
  (fun _ : Unit => Bool_false) (fun _ : Job => Bool_true) (fun _ : Job => Bool_false)
  (fun j1 j2 : Job =>
   Bool_not
     (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
        inst_3 JLFP j1 j2))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Model_Priority_Definitions_JLFP_policy Job
         inst_3 ->
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3) ->
       Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Analysis_Definitions_Overheads_PriorityBump_priority_bump Job
  inst_3 
  JLFP sched t
```
