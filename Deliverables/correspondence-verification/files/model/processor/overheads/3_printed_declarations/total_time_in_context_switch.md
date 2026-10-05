# `total_time_in_context_switch`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.overheads.total_time_in_context_switch`
- Lean: `Prosa.Model.Processor.Overheads.total_time_in_context_switch`
- Certificate: `ovh_total_time_in_context_switch_correspondence`

## Official Rocq

```coq
total_time_in_context_switch :
forall {Job : JobType}, @schedule Job (processor_state Job) -> instant -> instant -> nat

total_time_in_context_switch is not universe polymorphic
Arguments total_time_in_context_switch {Job} sched t1 t2
total_time_in_context_switch is transparent
Expands to: Constant prosa.model.processor.overheads.total_time_in_context_switch
Declared in library prosa.model.processor.overheads, line 160, characters 13-41
@total_time_in_context_switch
     : forall Job : JobType, @schedule Job (processor_state Job) -> instant -> instant -> nat
```

Body:

```coq
total_time_in_context_switch =
fun (Job : JobType) (sched : @schedule Job (processor_state Job)) (t1 t2 : instant) =>
\sum_(t1 <= t < t2) nat_of_bool (@is_context_switch Job sched t)
     : forall {Job : JobType}, @schedule Job (processor_state Job) -> instant -> instant -> nat

Arguments total_time_in_context_switch {Job} sched t1 t2
```

## Lean

```lean
@Prosa.Model.Processor.Overheads.total_time_in_context_switch : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job) →
      Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ
def Prosa.Model.Processor.Overheads.total_time_in_context_switch.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job) →
      Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ :=
fun {Job} [DecidableEq Job] sched t1 t2 =>
  ∑ t ∈ Finset.Ico t1 t2, (Prosa.Model.Processor.Overheads.is_context_switch sched t).toNat
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_Overheads_total_time_in_context_switch
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3) ->
       Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat
```

Body:

```coq
Prosa_Model_Processor_Overheads_total_time_in_context_switch@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : 
   DecidableEq Job)
  (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
             inst_3
             (Prosa_Model_Processor_Overheads_processor_state Job
                inst_3))
  (t1 t2 : Prosa_Behavior_Time_instant) =>
List_foldr_inst3 Nat Nat Nat_add (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
  (List_map_inst3 Prosa_Behavior_Time_instant Nat
     (fun t : Prosa_Behavior_Time_instant =>
      Bool_toNat
        (Prosa_Model_Processor_Overheads_is_context_switch Job
           inst_3
           sched t))
     (List_range' t1
        (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
           (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat) t2 t1)
        (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3) ->
       Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat

Arguments Prosa_Model_Processor_Overheads_total_time_in_context_switch Job
  inst_3 sched t1 t2
```
