# `processor_state`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.overheads.processor_state`
- Lean: `Prosa.Model.Processor.Overheads.processor_state`
- Certificate: `ovh_processor_state_correspondence`

## Official Rocq

```coq
processor_state : forall Job : JobType, ProcessorState Job

processor_state is not universe polymorphic
Arguments processor_state Job
processor_state is transparent
Expands to: Constant prosa.model.processor.overheads.processor_state
Declared in library prosa.model.processor.overheads, line 74, characters 21-36
processor_state
     : forall Job : JobType, ProcessorState Job
```

Body:

```coq
processor_state =
fun Job : JobType =>
{|
  State := proc_state Job;
  Core := Datatypes_unit__canonical__fintype_Finite;
  scheduled_on := overheads_scheduled_on Job;
  supply_on := overheads_supply_on Job;
  service_on := overheads_service_on Job;
  service_on_le_supply_on := fun j : Equality.sort Job => [eta overheads.processor_state_obligation_1 Job j];
  service_on_implies_scheduled_on :=
    fun j : Equality.sort Job => [eta overheads.processor_state_obligation_2 Job j]
|}
     : forall Job : JobType, ProcessorState Job

Arguments processor_state Job
```

## Lean

```lean
Prosa.Model.Processor.Overheads.processor_state : (Job : Prosa.Behavior.Job.JobType) →
  [inst : DecidableEq Job] → Prosa.Behavior.Schedule.ProcessorState Job
def Prosa.Model.Processor.Overheads.processor_state.{u_1} : (Job : Prosa.Behavior.Job.JobType) →
  [inst : DecidableEq Job] → Prosa.Behavior.Schedule.ProcessorState Job :=
fun Job [DecidableEq Job] =>
  { State := Prosa.Model.Processor.Overheads.proc_state Job, Core := Unit, coreFintype := inferInstance,
    coreDecidableEq := inferInstance, scheduled_on := Prosa.Model.Processor.Overheads.overheads_scheduled_on,
    supply_on := Prosa.Model.Processor.Overheads.overheads_supply_on,
    service_on := Prosa.Model.Processor.Overheads.overheads_service_on, service_on_le_supply_on := ⋯,
    service_on_implies_scheduled_on := ⋯ }
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_Overheads_processor_state
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_ProcessorState_inst2 Job
         inst_3
```

Body:

```coq
Prosa_Model_Processor_Overheads_processor_state@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job) =>
Prosa_Behavior_Schedule_ProcessorState_mk_inst2 Job
  inst_3
  (Prosa_Model_Processor_Overheads_proc_state Job) Unit
  (inferInstance (Fintype_inst1 Unit) PUnit_fintype_inst1)
  (inferInstance (DecidableEq Unit) instDecidableEqPUnit)
  (Prosa_Model_Processor_Overheads_overheads_scheduled_on Job
     inst_3)
  (Prosa_Model_Processor_Overheads_overheads_supply_on Job
     inst_3)
  (Prosa_Model_Processor_Overheads_overheads_service_on Job
     inst_3)
  (Prosa_Model_Processor_Overheads_processor_state__proof_1 Job
     inst_3)
  (Prosa_Model_Processor_Overheads_processor_state__proof_2 Job
     inst_3)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_ProcessorState_inst2 Job
         inst_3

Arguments Prosa_Model_Processor_Overheads_processor_state Job
  inst_3
```
