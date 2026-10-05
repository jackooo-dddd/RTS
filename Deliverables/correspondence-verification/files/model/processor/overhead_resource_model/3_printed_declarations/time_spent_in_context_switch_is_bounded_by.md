# `time_spent_in_context_switch_is_bounded_by`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.overhead_resource_model.time_spent_in_context_switch_is_bounded_by`
- Lean: `Prosa.Model.Processor.OverheadResourceModel.time_spent_in_context_switch_is_bounded_by`
- Certificate: `time_spent_in_context_switch_is_bounded_by_correspondence`

## Official Rocq

```coq
time_spent_in_context_switch_is_bounded_by :
forall {Job : JobType}, @schedule Job (processor_state Job) -> nat -> Prop

time_spent_in_context_switch_is_bounded_by is not universe polymorphic
Arguments time_spent_in_context_switch_is_bounded_by {Job} sched CSB%nat_scope
time_spent_in_context_switch_is_bounded_by is transparent
Expands to: Constant prosa.model.processor.overhead_resource_model.time_spent_in_context_switch_is_bounded_by
Declared in library prosa.model.processor.overhead_resource_model, line 50, characters 13-55
@time_spent_in_context_switch_is_bounded_by
     : forall Job : JobType, @schedule Job (processor_state Job) -> nat -> Prop
```

Body:

```coq
time_spent_in_context_switch_is_bounded_by =
fun (Job : JobType) (sched : @schedule Job (processor_state Job)) (CSB : nat) =>
forall (t1 t2 : instant) (oj : option (Equality.sort Job)),
is_true (@scheduled_job_invariant Job sched oj t1 t2) ->
is_true (@time_spent_in_context_switch Job sched oj t1 t2 <= CSB)
     : forall {Job : JobType}, @schedule Job (processor_state Job) -> nat -> Prop

Arguments time_spent_in_context_switch_is_bounded_by {Job} sched CSB%nat_scope
```

## Lean

```lean
@Prosa.Model.Processor.OverheadResourceModel.time_spent_in_context_switch_is_bounded_by : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job) → ℕ → Prop
```

Body:

```lean
def Prosa.Model.Processor.OverheadResourceModel.time_spent_in_context_switch_is_bounded_by.{u_1} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job) → ℕ → Prop :=
fun {Job} [DecidableEq Job] sched CSB =>
  ∀ (t1 t2 : Prosa.Behavior.Time.instant) (oj : Option Job),
    Prosa.Analysis.Definitions.Overheads.ScheduleChange.scheduled_job_invariant sched oj t1 t2 = true →
      Prosa.Model.Processor.OverheadResourceModel.time_spent_in_context_switch sched oj t1 t2 ≤ CSB
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_OverheadResourceModel_time_spent_in_context_switch_is_bounded_by
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3) ->
       Nat -> SProp
```

Body:

```coq
Prosa_Model_Processor_OverheadResourceModel_time_spent_in_context_switch_is_bounded_by@{u_1 Lean.u_1+1.0
Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
             inst_3
             (Prosa_Model_Processor_Overheads_processor_state Job
                inst_3))
  (CSB : Nat) =>
forall (t1 t2 : Prosa_Behavior_Time_instant) (oj : Option Job),
@eq Bool
  (Prosa_Analysis_Definitions_Overheads_ScheduleChange_scheduled_job_invariant Job
     inst_3 sched oj t1 t2)
  Bool_true ->
LE_le_inst1 Nat instLENat
  (Prosa_Model_Processor_OverheadResourceModel_time_spent_in_context_switch Job
     inst_3 sched oj t1 t2)
  CSB
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3) ->
       Nat -> SProp

Arguments Prosa_Model_Processor_OverheadResourceModel_time_spent_in_context_switch_is_bounded_by 
  Job inst_3 
  sched x____at___Init_Prelude3715277255__hygCtx13_Init_Prelude3715277255__hygCtx__hyg24%_Nat_scope
```
