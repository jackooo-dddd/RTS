# `no_schedule_changes_during`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.overheads.schedule_change.no_schedule_changes_during`
- Lean: `Prosa.Analysis.Definitions.Overheads.ScheduleChange.no_schedule_changes_during`
- Certificate: `no_schedule_changes_during_correspondence`

## Official Rocq

```coq
no_schedule_changes_during :
forall {Job : JobType}, @schedule Job (processor_state Job) -> instant -> instant -> bool

no_schedule_changes_during is not universe polymorphic
Arguments no_schedule_changes_during {Job} sched t1 t2
no_schedule_changes_during is transparent
Expands to: Constant prosa.analysis.definitions.overheads.schedule_change.no_schedule_changes_during
Declared in library prosa.analysis.definitions.overheads.schedule_change, line 32, characters 13-39
@no_schedule_changes_during
     : forall Job : JobType, @schedule Job (processor_state Job) -> instant -> instant -> bool
```

Body:

```coq
no_schedule_changes_during =
fun (Job : JobType) (sched : @schedule Job (processor_state Job)) (t1 t2 : instant) =>
@number_schedule_changes Job sched t1.+1 t2 == 0
     : forall {Job : JobType}, @schedule Job (processor_state Job) -> instant -> instant -> bool

Arguments no_schedule_changes_during {Job} sched t1 t2
```

## Lean

```lean
@Prosa.Analysis.Definitions.Overheads.ScheduleChange.no_schedule_changes_during : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job) →
      Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → Bool
def Prosa.Analysis.Definitions.Overheads.ScheduleChange.no_schedule_changes_during.{u_1} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job) →
      Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] sched t1 t2 =>
  decide (Prosa.Analysis.Definitions.Overheads.ScheduleChange.number_schedule_changes sched (t1 + 1) t2 = 0)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Overheads_ScheduleChange_no_schedule_changes_during
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3) ->
       Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Analysis_Definitions_Overheads_ScheduleChange_no_schedule_changes_during@{u_1 Lean.u_1+1.0
Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : 
   DecidableEq Job)
  (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
             inst_3
             (Prosa_Model_Processor_Overheads_processor_state Job
                inst_3))
  (t1 t2 : Prosa_Behavior_Time_instant) =>
Decidable_decide
  (@eq Nat
     (Prosa_Analysis_Definitions_Overheads_ScheduleChange_number_schedule_changes Job
        inst_3 sched
        (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
           (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
           (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1)))
        t2)
     (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))
  (instDecidableEqNat
     (Prosa_Analysis_Definitions_Overheads_ScheduleChange_number_schedule_changes Job
        inst_3 sched
        (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
           (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
           (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1)))
        t2)
     (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job),
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3) ->
       Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Analysis_Definitions_Overheads_ScheduleChange_no_schedule_changes_during 
  Job inst_3 
  sched t1 t
```
