# `pstate_instance`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.varspeed.pstate_instance`
- Lean: `Prosa.Model.Processor.Varspeed.pstate_instance`
- Certificate: `vs_processor_state_correspondence`

## Official Rocq

```coq
pstate_instance : forall Job : JobType, ProcessorState Job

pstate_instance is not universe polymorphic
Arguments pstate_instance Job
pstate_instance is transparent
Expands to: Constant prosa.model.processor.varspeed.pstate_instance
Declared in library prosa.model.processor.varspeed, line 60, characters 21-36
pstate_instance
     : forall Job : JobType, ProcessorState Job
```

Body:

```coq
pstate_instance =
fun Job : JobType =>
{|
  State := processor_state Job;
  Core := Datatypes_unit__canonical__fintype_Finite;
  scheduled_on := varspeed_scheduled_on Job;
  supply_on := varspeed_supply_on Job;
  service_on := varspeed_service_on Job;
  service_on_le_supply_on := fun j : Equality.sort Job => [eta varspeed.pstate_instance_obligation_1 Job j];
  service_on_implies_scheduled_on :=
    fun j : Equality.sort Job => [eta varspeed.pstate_instance_obligation_2 Job j]
|}
     : forall Job : JobType, ProcessorState Job

Arguments pstate_instance Job
```

## Lean

```lean
Prosa.Model.Processor.Varspeed.pstate_instance : (Job : Prosa.Behavior.Job.JobType) →
  [inst : DecidableEq Job] → Prosa.Behavior.Schedule.ProcessorState Job
def Prosa.Model.Processor.Varspeed.pstate_instance.{u_1} : (Job : Prosa.Behavior.Job.JobType) →
  [inst : DecidableEq Job] → Prosa.Behavior.Schedule.ProcessorState Job :=
fun Job [DecidableEq Job] =>
  { State := Prosa.Model.Processor.Varspeed.processor_state Job, Core := Unit, coreFintype := inferInstance,
    coreDecidableEq := inferInstance,
    scheduled_on := fun j s r => Prosa.Model.Processor.Varspeed.varspeed_scheduled_on j s r,
    supply_on := fun s r => Prosa.Model.Processor.Varspeed.varspeed_supply_on s r,
    service_on := fun j s r => Prosa.Model.Processor.Varspeed.varspeed_service_on j s r, service_on_le_supply_on := ⋯,
    service_on_implies_scheduled_on := ⋯ }
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_Varspeed_pstate_instance
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_ProcessorState_inst2 Job
         inst_3
```

Body:

```coq
Prosa_Model_Processor_Varspeed_pstate_instance@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job) =>
Prosa_Behavior_Schedule_ProcessorState_mk_inst2 Job
  inst_3
  (Prosa_Model_Processor_Varspeed_processor_state Job) Unit
  (inferInstance (Fintype_inst1 Unit) PUnit_fintype_inst1)
  (inferInstance (DecidableEq Unit) instDecidableEqPUnit)
  (fun (j : Job) (s : Prosa_Model_Processor_Varspeed_processor_state Job) (r : Unit) =>
   Prosa_Model_Processor_Varspeed_varspeed_scheduled_on Job
     inst_3 j s r)
  (fun (s : Prosa_Model_Processor_Varspeed_processor_state Job) (r : Unit) =>
   Prosa_Model_Processor_Varspeed_varspeed_supply_on Job
     inst_3 s r)
  (fun (j : Job) (s : Prosa_Model_Processor_Varspeed_processor_state Job) (r : Unit) =>
   Prosa_Model_Processor_Varspeed_varspeed_service_on Job
     inst_3 j s r)
  (Prosa_Model_Processor_Varspeed_pstate_instance__proof_1 Job
     inst_3)
  (Prosa_Model_Processor_Varspeed_pstate_instance__proof_2 Job
     inst_3)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_ProcessorState_inst2 Job
         inst_3

Arguments Prosa_Model_Processor_Varspeed_pstate_instance Job
  inst_3
```
