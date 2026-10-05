# `blackout_during`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.supply.blackout_during`
- Lean: `Prosa.Model.Processor.Supply.blackout_during`
- Certificate: ``

## Official Rocq

```coq
blackout_during :
forall {Job : JobType} {PState : ProcessorState Job}, @schedule Job PState -> instant -> instant -> nat

blackout_during is not universe polymorphic
Arguments blackout_during {Job PState} sched t1 t2
blackout_during is transparent
Expands to: Constant prosa.model.processor.supply.blackout_during
Declared in library prosa.model.processor.supply, line 33, characters 13-28
@blackout_during
     : forall (Job : JobType) (PState : ProcessorState Job),
       @schedule Job PState -> instant -> instant -> nat
```

Body:

```coq
blackout_during =
fun (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) (t1 t2 : instant) =>
\sum_(t1 <= t < t2) nat_of_bool (@is_blackout Job PState sched t)
     : forall {Job : JobType} {PState : ProcessorState Job},
       @schedule Job PState -> instant -> instant -> nat

Arguments blackout_during {Job PState} sched t1 t2
```

## Lean

```lean
@Prosa.Model.Processor.Supply.blackout_during : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ
def Prosa.Model.Processor.Supply.blackout_during.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState → Prosa.Behavior.Time.instant → Prosa.Behavior.Time.instant → ℕ :=
fun {Job} [DecidableEq Job] {PState} sched t1 t2 =>
  ∑ t ∈ Finset.Ico t1 t2, (Prosa.Model.Processor.Supply.is_blackout sched t).toNat
```

## Lean, imported into Rocq

```coq
ImportedSupply.Prosa_Model_Processor_Supply_blackout_during
     : forall (Job : ImportedSupply.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedSupply.DecidableEq Job)
         (PState : ImportedSupply.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedSupply.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       ImportedSupply.Prosa_Behavior_Time_instant -> ImportedSupply.Prosa_Behavior_Time_instant -> Nat
```

Body:

```coq
ImportedSupply.Prosa_Model_Processor_Supply_blackout_during@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : ImportedSupply.Prosa_Behavior_Job_JobType)
  (inst_3 : 
   ImportedSupply.DecidableEq Job)
  (PState : ImportedSupply.Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (sched : ImportedSupply.Prosa_Behavior_Schedule_schedule Job
             inst_3
             PState)
  (t1 t2 : ImportedSupply.Prosa_Behavior_Time_instant) =>
ImportedSupply.List_foldr_inst3 Nat Nat Nat_add
  (ImportedSupply.OfNat_ofNat_inst1 Nat 0 (ImportedSupply.instOfNatNat 0))
  (ImportedSupply.List_map_inst3 ImportedSupply.Prosa_Behavior_Time_instant Nat
     (fun t : ImportedSupply.Prosa_Behavior_Time_instant =>
      ImportedSupply.Bool_toNat
        (ImportedSupply.Prosa_Validation_SupplyInterface_isBlackoutProjection Job
           inst_3
           PState sched t))
     (ImportedSupply.List_range' t1
        (ImportedSupply.HSub_hSub_inst7 ImportedSupply.Prosa_Behavior_Time_instant
           ImportedSupply.Prosa_Behavior_Time_instant ImportedSupply.Prosa_Behavior_Time_instant
           (ImportedSupply.instHSub_inst1 ImportedSupply.Prosa_Behavior_Time_instant
              ImportedSupply.instSubNat)
           t2 t1)
        (ImportedSupply.OfNat_ofNat_inst1 Nat 1 (ImportedSupply.instOfNatNat 1))))
     : forall (Job : ImportedSupply.Prosa_Behavior_Job_JobType)
         (inst_3 : ImportedSupply.DecidableEq Job)
         (PState : ImportedSupply.Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       ImportedSupply.Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       ImportedSupply.Prosa_Behavior_Time_instant -> ImportedSupply.Prosa_Behavior_Time_instant -> Nat

Arguments ImportedSupply.Prosa_Model_Processor_Supply_blackout_during Job
  inst_3 PState sched 
  t1 t2
```
