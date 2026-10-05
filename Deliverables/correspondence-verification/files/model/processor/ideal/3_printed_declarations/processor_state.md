# `processor_state`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.ideal.processor_state`
- Lean: `Prosa.Model.Processor.Ideal.processor_state`
- Certificate: `ideal_processor_state_correspondence`

## Official Rocq

```coq
processor_state : forall Job : JobType, ProcessorState Job

processor_state is not universe polymorphic
Arguments processor_state Job
processor_state is transparent
Expands to: Constant prosa.model.processor.ideal.processor_state
Declared in library prosa.model.processor.ideal, line 22, characters 21-36
processor_state
     : forall Job : JobType, ProcessorState Job
```

Body:

```coq
processor_state =
fun Job : JobType =>
{|
  State := option (Equality.sort Job);
  Core := Datatypes_unit__canonical__fintype_Finite;
  scheduled_on :=
    fun (j : Equality.sort Job) (s : option (Equality.sort Job)) => fun=> s == @Some (Equality.sort Job) j;
  supply_on := fun=> (fun=> 1);
  service_on :=
    fun (j : Equality.sort Job) (s : option (Equality.sort Job)) =>
    fun=> (if s == @Some (Equality.sort Job) j then 1 else 0);
  service_on_le_supply_on :=
    fun (j : Equality.sort Job) (s : option (Equality.sort Job)) =>
    fun=> ideal.processor_state_obligation_1 Job j s;
  service_on_implies_scheduled_on :=
    fun (j : Equality.sort Job) (s : option (Equality.sort Job)) =>
    fun=> ideal.processor_state_obligation_2 Job j s
|}
     : forall Job : JobType, ProcessorState Job

Arguments processor_state Job
```

## Lean

```lean
Prosa.Model.Processor.Ideal.processor_state : (Job : Prosa.Behavior.Job.JobType) →
  [inst : DecidableEq Job] → Prosa.Behavior.Schedule.ProcessorState Job
def Prosa.Model.Processor.Ideal.processor_state.{u_1} : (Job : Prosa.Behavior.Job.JobType) →
  [inst : DecidableEq Job] → Prosa.Behavior.Schedule.ProcessorState Job :=
fun Job [DecidableEq Job] =>
  { State := Option Job, Core := Unit, coreFintype := inferInstance, coreDecidableEq := inferInstance,
    scheduled_on := fun j s x => decide (s = some j), supply_on := fun x x_1 => 1,
    service_on := fun j s x => if decide (s = some j) = true then 1 else 0, service_on_le_supply_on := ⋯,
    service_on_implies_scheduled_on := ⋯ }
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_Ideal_processor_state
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_ProcessorState_inst2 Job
         inst_3
```

Body:

```coq
Prosa_Model_Processor_Ideal_processor_state@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job) =>
Prosa_Behavior_Schedule_ProcessorState_mk_inst2 Job
  inst_3 (Option Job) Unit
  (inferInstance (Fintype_inst1 Unit) PUnit_fintype_inst1)
  (inferInstance (DecidableEq Unit) instDecidableEqPUnit)
  (fun (j : Job) (s : Option Job) (_ : Unit) =>
   Decidable_decide (@eq (Option Job) s (Option_some Job j))
     (Option_instDecidableEq Job inst_3 s
        (Option_some Job j)))
  (fun (_ : Option Job) (_ : Unit) => OfNat_ofNat_inst1 Prosa_Behavior_Job_work 1 (instOfNatNat 1))
  (fun (j : Job) (s : Option Job) (_ : Unit) =>
   ite Prosa_Behavior_Job_work
     (@eq Bool
        (Decidable_decide (@eq (Option Job) s (Option_some Job j))
           (Option_instDecidableEq Job inst_3 s
              (Option_some Job j)))
        Bool_true)
     (instDecidableEqBool
        (Decidable_decide (@eq (Option Job) s (Option_some Job j))
           (Option_instDecidableEq Job inst_3 s
              (Option_some Job j)))
        Bool_true)
     (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 1 (instOfNatNat 1))
     (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0)))
  (Prosa_Model_Processor_Ideal_processor_state__proof_1 Job
     inst_3)
  (Prosa_Model_Processor_Ideal_processor_state__proof_2 Job
     inst_3)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_ProcessorState_inst2 Job
         inst_3

Arguments Prosa_Model_Processor_Ideal_processor_state Job
  inst_3
```
