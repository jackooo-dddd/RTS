# `exceedance_proc_state`

- Kind (Rocq): Instance
- Rocq: `prosa.model.processor.ideal_uni_exceed.exceedance_proc_state`
- Lean: `Prosa.Model.Processor.IdealUniExceed.exceedance_proc_state`
- Certificate: `iue_processor_state_correspondence`

## Official Rocq

```coq
exceedance_proc_state : forall Job : JobType, ProcessorState Job

exceedance_proc_state is not universe polymorphic
Arguments exceedance_proc_state Job
exceedance_proc_state is transparent
Expands to: Constant prosa.model.processor.ideal_uni_exceed.exceedance_proc_state
Declared in library prosa.model.processor.ideal_uni_exceed, line 94, characters 2-259
exceedance_proc_state
     : forall Job : JobType, ProcessorState Job
```

Body:

```coq
exceedance_proc_state =
fun Job : JobType =>
{|
  State := @exceedance_processor_state Job;
  Core := Datatypes_unit__canonical__fintype_Finite;
  scheduled_on := @exceedance_scheduled_on Job;
  supply_on := @exceedance_supply_on Job;
  service_on := @exceedance_service_on Job;
  service_on_le_supply_on :=
    fun j : Equality.sort Job => [eta @ideal_uni_exceed.exceedance_proc_state_obligation_1 Job j];
  service_on_implies_scheduled_on :=
    fun j : Equality.sort Job => [eta @ideal_uni_exceed.exceedance_proc_state_obligation_2 Job j]
|}
     : forall Job : JobType, ProcessorState Job

Arguments exceedance_proc_state Job
```

## Lean

```lean
Prosa.Model.Processor.IdealUniExceed.exceedance_proc_state : (Job : Prosa.Behavior.Job.JobType) →
  [inst : DecidableEq Job] → Prosa.Behavior.Schedule.ProcessorState Job
@[instance_reducible] def Prosa.Model.Processor.IdealUniExceed.exceedance_proc_state.{u_1} : (Job :
    Prosa.Behavior.Job.JobType) →
  [inst : DecidableEq Job] → Prosa.Behavior.Schedule.ProcessorState Job :=
fun Job [DecidableEq Job] =>
  { State := Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state Job, Core := Unit,
    coreFintype := inferInstance, coreDecidableEq := inferInstance,
    scheduled_on := Prosa.Model.Processor.IdealUniExceed.exceedance_scheduled_on,
    supply_on := Prosa.Model.Processor.IdealUniExceed.exceedance_supply_on,
    service_on := Prosa.Model.Processor.IdealUniExceed.exceedance_service_on, service_on_le_supply_on := ⋯,
    service_on_implies_scheduled_on := ⋯ }
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_ProcessorState_inst2 Job
         inst_3
```

Body:

```coq
Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job) =>
Prosa_Behavior_Schedule_ProcessorState_mk_inst2 Job
  inst_3
  (Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state Job) Unit
  (inferInstance (Fintype_inst1 Unit) PUnit_fintype_inst1)
  (inferInstance (DecidableEq Unit) instDecidableEqPUnit)
  (Prosa_Model_Processor_IdealUniExceed_exceedance_scheduled_on Job
     inst_3)
  (Prosa_Model_Processor_IdealUniExceed_exceedance_supply_on Job
     inst_3)
  (Prosa_Model_Processor_IdealUniExceed_exceedance_service_on Job
     inst_3)
  (Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state__proof_1 Job
     inst_3)
  (Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state__proof_2 Job
     inst_3)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_ProcessorState_inst2 Job
         inst_3

Arguments Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state Job
  inst_3
```
