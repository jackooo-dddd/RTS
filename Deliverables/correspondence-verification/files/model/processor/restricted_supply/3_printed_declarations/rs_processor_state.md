# `rs_processor_state`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.restricted_supply.rs_processor_state`
- Lean: `Prosa.Model.Processor.RestrictedSupply.rs_processor_state`
- Certificate: `rs_processor_state_correspondence`

## Official Rocq

```coq
rs_processor_state : forall Job : JobType, ProcessorState Job

rs_processor_state is not universe polymorphic
Arguments rs_processor_state Job
rs_processor_state is transparent
Expands to: Constant prosa.model.processor.restricted_supply.rs_processor_state
Declared in library prosa.model.processor.restricted_supply, line 65, characters 21-39
rs_processor_state
     : forall Job : JobType, ProcessorState Job
```

Body:

```coq
rs_processor_state =
fun Job : JobType =>
{|
  State := @processor_state Job;
  Core := Datatypes_unit__canonical__fintype_Finite;
  scheduled_on := fun (j : Equality.sort Job) (s : @processor_state Job) => fun=> rs_scheduled_on Job j s;
  supply_on := fun s : @processor_state Job => fun=> rs_supply_on Job s;
  service_on := fun (j : Equality.sort Job) (s : @processor_state Job) => fun=> rs_service_on Job j s;
  service_on_le_supply_on :=
    fun (j : Equality.sort Job) (s : @processor_state Job) =>
    [eta restricted_supply.rs_processor_state_obligation_1 Job j s];
  service_on_implies_scheduled_on :=
    fun (j : Equality.sort Job) (s : @processor_state Job) =>
    [eta restricted_supply.rs_processor_state_obligation_2 Job j s]
|}
     : forall Job : JobType, ProcessorState Job

Arguments rs_processor_state Job
```

## Lean

```lean
Prosa.Model.Processor.RestrictedSupply.rs_processor_state : (Job : Prosa.Behavior.Job.JobType) →
  [inst : DecidableEq Job] → Prosa.Behavior.Schedule.ProcessorState Job
def Prosa.Model.Processor.RestrictedSupply.rs_processor_state.{u_1} : (Job : Prosa.Behavior.Job.JobType) →
  [inst : DecidableEq Job] → Prosa.Behavior.Schedule.ProcessorState Job :=
fun Job [DecidableEq Job] =>
  { State := Prosa.Model.Processor.RestrictedSupply.processor_state Job, Core := Unit, coreFintype := inferInstance,
    coreDecidableEq := inferInstance,
    scheduled_on := fun j s x => Prosa.Model.Processor.RestrictedSupply.rs_scheduled_on j s,
    supply_on := fun s x => Prosa.Model.Processor.RestrictedSupply.rs_supply_on s,
    service_on := fun j s x => Prosa.Model.Processor.RestrictedSupply.rs_service_on j s, service_on_le_supply_on := ⋯,
    service_on_implies_scheduled_on := ⋯ }
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_RestrictedSupply_rs_processor_state
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_ProcessorState_inst2 Job
         inst_3
```

Body:

```coq
Prosa_Model_Processor_RestrictedSupply_rs_processor_state@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job) =>
Prosa_Behavior_Schedule_ProcessorState_mk_inst2 Job
  inst_3
  (Prosa_Model_Processor_RestrictedSupply_processor_state Job) Unit
  (inferInstance (Fintype_inst1 Unit) PUnit_fintype_inst1)
  (inferInstance (DecidableEq Unit) instDecidableEqPUnit)
  (fun (j : Job) (s : Prosa_Model_Processor_RestrictedSupply_processor_state Job) (_ : Unit) =>
   Prosa_Model_Processor_RestrictedSupply_rs_scheduled_on Job
     inst_3 j s)
  (fun (s : Prosa_Model_Processor_RestrictedSupply_processor_state Job) (_ : Unit) =>
   Prosa_Model_Processor_RestrictedSupply_rs_supply_on Job
     inst_3 s)
  (fun (j : Job) (s : Prosa_Model_Processor_RestrictedSupply_processor_state Job) (_ : Unit) =>
   Prosa_Model_Processor_RestrictedSupply_rs_service_on Job
     inst_3 j s)
  (Prosa_Model_Processor_RestrictedSupply_rs_processor_state__proof_1 Job
     inst_3)
  (Prosa_Model_Processor_RestrictedSupply_rs_processor_state__proof_2 Job
     inst_3)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_ProcessorState_inst2 Job
         inst_3

Arguments Prosa_Model_Processor_RestrictedSupply_rs_processor_state Job
  inst_3
```
