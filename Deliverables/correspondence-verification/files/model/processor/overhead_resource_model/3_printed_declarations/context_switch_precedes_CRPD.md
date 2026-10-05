# `context_switch_precedes_CRPD`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.overhead_resource_model.context_switch_precedes_CRPD`
- Lean: `Prosa.Model.Processor.OverheadResourceModel.context_switch_precedes_CRPD`
- Certificate: `context_switch_precedes_CRPD_correspondence`

## Official Rocq

```coq
context_switch_precedes_CRPD : forall {Job : JobType}, @schedule Job (processor_state Job) -> Prop

context_switch_precedes_CRPD is not universe polymorphic
Arguments context_switch_precedes_CRPD {Job} sched
context_switch_precedes_CRPD is transparent
Expands to: Constant prosa.model.processor.overhead_resource_model.context_switch_precedes_CRPD
Declared in library prosa.model.processor.overhead_resource_model, line 87, characters 13-41
@context_switch_precedes_CRPD
     : forall Job : JobType, @schedule Job (processor_state Job) -> Prop
```

Body:

```coq
context_switch_precedes_CRPD =
fun (Job : JobType) (sched : @schedule Job (processor_state Job)) =>
forall (oj : option (Equality.sort Job)) (t1 t2 : instant),
is_true (@scheduled_job_invariant Job sched oj t1 t2) ->
forall t : nat,
is_true (t1 <= t < t2) ->
is_true (@is_context_switch Job sched t) ->
forall t' : nat, is_true (t1 <= t' <= t) -> is_true (~~ @is_CRPD Job sched t')
     : forall {Job : JobType}, @schedule Job (processor_state Job) -> Prop

Arguments context_switch_precedes_CRPD {Job} sched
```

## Lean

```lean
@Prosa.Model.Processor.OverheadResourceModel.context_switch_precedes_CRPD : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job) → Prop
```

Body:

```lean
def Prosa.Model.Processor.OverheadResourceModel.context_switch_precedes_CRPD.{u_1} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job) → Prop :=
fun {Job} [DecidableEq Job] sched =>
  ∀ (oj : Option Job) (t1 t2 : Prosa.Behavior.Time.instant),
    Prosa.Analysis.Definitions.Overheads.ScheduleChange.scheduled_job_invariant sched oj t1 t2 = true →
      ∀ (t : ℕ),
        (decide (t1 ≤ t) && decide (t < t2)) = true →
          Prosa.Model.Processor.Overheads.is_context_switch sched t = true →
            ∀ (t' : ℕ),
              (decide (t1 ≤ t') && decide (t' ≤ t)) = true → (!Prosa.Model.Processor.Overheads.is_CRPD sched t') = true
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_OverheadResourceModel_context_switch_precedes_CRPD
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3) ->
       SProp
```

Body:

```coq
Prosa_Model_Processor_OverheadResourceModel_context_switch_precedes_CRPD@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
             inst_3
             (Prosa_Model_Processor_Overheads_processor_state Job
                inst_3)) =>
forall (oj : Option Job) (t1 t2 : Prosa_Behavior_Time_instant),
@eq Bool
  (Prosa_Analysis_Definitions_Overheads_ScheduleChange_scheduled_job_invariant Job
     inst_3 sched oj t1 t2)
  Bool_true ->
forall t : Nat,
@eq Bool
  (Bool_and (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t) (Nat_decLe t1 t))
     (Decidable_decide (LT_lt_inst1 Nat instLTNat t t2) (Nat_decLt t t2)))
  Bool_true ->
@eq Bool
  (Prosa_Model_Processor_Overheads_is_context_switch Job
     inst_3 sched t)
  Bool_true ->
forall t' : Nat,
@eq Bool
  (Bool_and (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1 t') (Nat_decLe t1 t'))
     (Decidable_decide (LE_le_inst1 Nat instLENat t' t) (Nat_decLe t' t)))
  Bool_true ->
@eq Bool
  (Bool_not
     (Prosa_Model_Processor_Overheads_is_CRPD Job
        inst_3 sched t'))
  Bool_true
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3) ->
       SProp

Arguments Prosa_Model_Processor_OverheadResourceModel_context_switch_precedes_CRPD 
  Job inst_3 
  sched
```
