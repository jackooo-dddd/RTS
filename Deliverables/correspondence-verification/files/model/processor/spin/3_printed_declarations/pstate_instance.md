# `pstate_instance`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.spin.pstate_instance`
- Lean: `Prosa.Model.Processor.Spin.pstate_instance`
- Certificate: `pstate_instance_correspondence`

## Official Rocq

```coq
pstate_instance : forall Job : JobType, ProcessorState Job

pstate_instance is not universe polymorphic
Arguments pstate_instance Job
pstate_instance is transparent
Expands to: Constant prosa.model.processor.spin.pstate_instance
Declared in library prosa.model.processor.spin, line 63, characters 21-36
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
  scheduled_on := spin_scheduled_on Job;
  supply_on := spin_supply_on Job;
  service_on := spin_service_on Job;
  service_on_le_supply_on := fun j : Equality.sort Job => [eta spin.pstate_instance_obligation_1 Job j];
  service_on_implies_scheduled_on :=
    fun j : Equality.sort Job => [eta spin.pstate_instance_obligation_2 Job j]
|}
     : forall Job : JobType, ProcessorState Job

Arguments pstate_instance Job
```

## Lean

```lean
Prosa.Model.Processor.Spin.pstate_instance : (Job : Prosa.Behavior.Job.JobType) →
  [inst : DecidableEq Job] → Prosa.Behavior.Schedule.ProcessorState Job
def Prosa.Model.Processor.Spin.pstate_instance.{u_1} : (Job : Prosa.Behavior.Job.JobType) →
  [inst : DecidableEq Job] → Prosa.Behavior.Schedule.ProcessorState Job :=
fun Job [DecidableEq Job] =>
  { State := Prosa.Model.Processor.Spin.processor_state Job, Core := Unit, coreFintype := inferInstance,
    coreDecidableEq := inferInstance, scheduled_on := Prosa.Model.Processor.Spin.spin_scheduled_on,
    supply_on := Prosa.Model.Processor.Spin.spin_supply_on, service_on := Prosa.Model.Processor.Spin.spin_service_on,
    service_on_le_supply_on := ⋯, service_on_implies_scheduled_on := ⋯ }
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_Spin_pstate_instance
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_ProcessorState_inst2 Job
         inst_3
```

Body:

```coq
Prosa_Model_Processor_Spin_pstate_instance@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job) =>
Prosa_Behavior_Schedule_ProcessorState_mk_inst2 Job
  inst_3
  (Prosa_Model_Processor_Spin_processor_state Job) Unit
  (inferInstance (Fintype_inst1 Unit) PUnit_fintype_inst1)
  (inferInstance (DecidableEq Unit) instDecidableEqPUnit)
  (Prosa_Model_Processor_Spin_spin_scheduled_on Job
     inst_3)
  (Prosa_Model_Processor_Spin_spin_supply_on Job
     inst_3)
  (Prosa_Model_Processor_Spin_spin_service_on Job
     inst_3)
  (Prosa_Model_Processor_Spin_pstate_instance__proof_1 Job
     inst_3)
  (Prosa_Model_Processor_Spin_pstate_instance__proof_2 Job
     inst_3)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_ProcessorState_inst2 Job
         inst_3

Arguments Prosa_Model_Processor_Spin_pstate_instance Job
  inst_3
```
