# `time_spent_in_dispatch`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.overhead_resource_model.time_spent_in_dispatch`
- Lean: `Prosa.Model.Processor.OverheadResourceModel.time_spent_in_dispatch`
- Certificate: `time_spent_in_dispatch_correspondence`

## Official Rocq

```coq
time_spent_in_dispatch :
forall {Job : JobType},
@schedule Job (processor_state Job) -> option (Equality.sort Job) -> instant -> instant -> nat

time_spent_in_dispatch is not universe polymorphic
Arguments time_spent_in_dispatch {Job} sched oj t1 t2
time_spent_in_dispatch is transparent
Expands to: Constant prosa.model.processor.overhead_resource_model.time_spent_in_dispatch
Declared in library prosa.model.processor.overhead_resource_model, line 24, characters 13-35
@time_spent_in_dispatch
     : forall Job : JobType,
       @schedule Job (processor_state Job) -> option (Equality.sort Job) -> instant -> instant -> nat
```

Body:

```coq
time_spent_in_dispatch =
fun (Job : JobType) (sched : @schedule Job (processor_state Job)) (oj : option (Equality.sort Job))
  (t1 t2 : instant) =>
\sum_(t1 <= t < t2) nat_of_bool ((@scheduled_job Job sched t == oj) && @is_dispatch Job sched t)
     : forall {Job : JobType},
       @schedule Job (processor_state Job) -> option (Equality.sort Job) -> instant -> instant -> nat

Arguments time_spent_in_dispatch {Job} sched oj t1 t2
```

## Lean

```lean
@Prosa.Model.Processor.OverheadResourceModel.time_spent_in_dispatch : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job) →
      Option Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ
```

Body:

```lean
def Prosa.Model.Processor.OverheadResourceModel.time_spent_in_dispatch.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Overheads.processor_state Job) →
      Option Job → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ :=
fun {Job} [DecidableEq Job] sched oj t1 t2 =>
  ∑ t ∈ Finset.Ico t1 t2,
    (decide (Prosa.Model.Processor.Overheads.scheduled_job sched t = oj) &&
        Prosa.Model.Processor.Overheads.is_dispatch sched t).toNat
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_OverheadResourceModel_time_spent_in_dispatch
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_schedule_inst4 Job
         inst_3
         (Prosa_Model_Processor_Overheads_processor_state Job
            inst_3) ->
       Option Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat
```

Body:

```coq
Prosa_Model_Processor_OverheadResourceModel_time_spent_in_dispatch@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : 
   DecidableEq Job)
  (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
             inst_3
             (Prosa_Model_Processor_Overheads_processor_state Job
                inst_3))
  (oj : Option Job) (t1 t2 : Prosa_Behavior_Time_instant) =>
List_foldr_inst3 Nat Nat Nat_add (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
  (List_map_inst3 Prosa_Behavior_Time_instant Nat
     (fun t : Prosa_Behavior_Time_instant =>
      Bool_toNat
        (Bool_and
           (Decidable_decide
              (@eq (Option Job)
                 (Prosa_Model_Processor_Overheads_scheduled_job Job
                    inst_3
                    sched t)
                 oj)
              (Option_instDecidableEq Job
                 inst_3
                 (Prosa_Model_Processor_Overheads_scheduled_job Job
                    inst_3
                    sched t)
                 oj))
           (Prosa_Model_Processor_Overheads_is_dispatch Job
              inst_3
              sched t)))
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
       Option Job -> Prosa_Behavior_Time_instant -> Prosa_Behavior_Time_instant -> Nat

Arguments Prosa_Model_Processor_OverheadResourceModel_time_spent_in_dispatch Job
  inst_3 
  sched oj t1 t2
```
