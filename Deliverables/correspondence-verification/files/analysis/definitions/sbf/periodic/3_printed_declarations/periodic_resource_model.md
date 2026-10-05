# `periodic_resource_model`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.sbf.periodic.periodic_resource_model`
- Lean: `Prosa.Analysis.Definitions.Sbf.Periodic.periodic_resource_model`
- Certificate: `periodic_resource_model_correspondence`

## Official Rocq

```coq
periodic_resource_model :
forall {Job : JobType} {PState : ProcessorState Job}, duration -> duration -> @schedule Job PState -> Prop

periodic_resource_model is not universe polymorphic
Arguments periodic_resource_model {Job PState} Π γ sched
periodic_resource_model is transparent
Expands to: Constant prosa.analysis.definitions.sbf.periodic.periodic_resource_model
Declared in library prosa.analysis.definitions.sbf.periodic, line 17, characters 13-36
@periodic_resource_model
     : forall (Job : JobType) (PState : ProcessorState Job),
       duration -> duration -> @schedule Job PState -> Prop
```

Body:

```coq
periodic_resource_model =
fun (Job : JobType) (PState : ProcessorState Job) (Π γ : duration) (sched : @schedule Job PState) =>
is_true (0 < Π) /\
is_true (γ <= Π) /\ (forall k : nat, is_true (γ <= @supply_during Job PState sched (Π * k) (Π * (k + 1))))
     : forall {Job : JobType} {PState : ProcessorState Job},
       duration -> duration -> @schedule Job PState -> Prop

Arguments periodic_resource_model {Job PState} Π γ sched
```

## Lean

```lean
@Prosa.Analysis.Definitions.Sbf.Periodic.periodic_resource_model : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Schedule.schedule PState → Prop
def Prosa.Analysis.Definitions.Sbf.Periodic.periodic_resource_model.{u_1, u_2, u_3} : {Job :
    Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Schedule.schedule PState → Prop :=
fun {Job} [DecidableEq Job] {PState} period allocation sched =>
  period > 0 ∧
    period ≥ allocation ∧
      ∀ (k : ℕ), Prosa.Model.Processor.Supply.supply_during sched (period * k) (period * (k + 1)) ≥ allocation
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Sbf_Periodic_periodic_resource_model
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       SProp
```

Body:

```coq
Prosa_Analysis_Definitions_Sbf_Periodic_periodic_resource_model@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (period allocation : Prosa_Behavior_Time_duration)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState) =>
And
  (GT_gt_inst1 Prosa_Behavior_Time_duration instLTNat period
     (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0)))
  (And (GE_ge_inst1 Prosa_Behavior_Time_duration instLENat period allocation)
     (forall k : Nat,
      GE_ge_inst1 Prosa_Behavior_Job_work instLENat
        (Prosa_Model_Processor_Supply_supply_during Job
           inst_3 PState sched
           (HMul_hMul_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
              (instHMul_inst1 Prosa_Behavior_Time_duration instMulNat) period k)
           (HMul_hMul_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
              (instHMul_inst1 Prosa_Behavior_Time_duration instMulNat) period
              (HAdd_hAdd_inst7 Nat Prosa_Behavior_Time_instant Nat (instHAdd_inst1 Nat instAddNat) k
                 (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1)))))
        allocation))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       SProp

Arguments Prosa_Analysis_Definitions_Sbf_Periodic_periodic_resource_model Job
  inst_3 PState 
  period allocation sched
```
