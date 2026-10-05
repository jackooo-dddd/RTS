# `spin_supply_on`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.spin.spin_supply_on`
- Lean: `Prosa.Model.Processor.Spin.spin_supply_on`
- Certificate: `spin_supply_on_correspondence`

## Official Rocq

```coq
spin_supply_on : forall Job : JobType, processor_state Job -> unit -> work

spin_supply_on is not universe polymorphic
Arguments spin_supply_on Job s _
spin_supply_on is transparent
Expands to: Constant prosa.model.processor.spin.spin_supply_on
Declared in library prosa.model.processor.spin, line 43, characters 15-29
spin_supply_on
     : forall Job : JobType, processor_state Job -> unit -> work
```

Body:

```coq
spin_supply_on =
fun (Job : JobType) (s : processor_state Job) => fun=> match s with
                                                       | @Spin _ _ => 0
                                                       | _ => 1
                                                       end
     : forall Job : JobType, processor_state Job -> unit -> work

Arguments spin_supply_on Job s _
```

## Lean

```lean
@Prosa.Model.Processor.Spin.spin_supply_on : {Job : Prosa.Behavior.Job.JobType} →
  [DecidableEq Job] → Prosa.Model.Processor.Spin.processor_state Job → Unit → Prosa.Behavior.Job.work
def Prosa.Model.Processor.Spin.spin_supply_on.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [DecidableEq Job] → Prosa.Model.Processor.Spin.processor_state Job → Unit → Prosa.Behavior.Job.work :=
fun {Job} [DecidableEq Job] s x =>
  match s with
  | Prosa.Model.Processor.Spin.processor_state.Idle => 1
  | Prosa.Model.Processor.Spin.processor_state.Progress j => 1
  | Prosa.Model.Processor.Spin.processor_state.Spin j => 0
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_Spin_spin_supply_on
     : forall Job : Prosa_Behavior_Job_JobType,
       DecidableEq Job -> Prosa_Model_Processor_Spin_processor_state Job -> Unit -> Prosa_Behavior_Job_work
```

Body:

```coq
Prosa_Model_Processor_Spin_spin_supply_on@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType) (_ : DecidableEq Job)
  (s : Prosa_Model_Processor_Spin_processor_state Job) (_ : Unit) =>
Prosa_Model_Processor_Spin_spin_supply_on_match_1 Job
  (fun _ : Prosa_Model_Processor_Spin_processor_state Job => Prosa_Behavior_Job_work) s
  (fun _ : Unit => OfNat_ofNat_inst1 Prosa_Behavior_Job_work 1 (instOfNatNat 1))
  (fun _ : Job => OfNat_ofNat_inst1 Prosa_Behavior_Job_work 1 (instOfNatNat 1))
  (fun _ : Job => OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
     : forall Job : Prosa_Behavior_Job_JobType,
       DecidableEq Job -> Prosa_Model_Processor_Spin_processor_state Job -> Unit -> Prosa_Behavior_Job_work

Arguments Prosa_Model_Processor_Spin_spin_supply_on Job
  inst_3 s
  x____at___Prosa_Model_Processor_Spin793384949__hygCtx__hyg8
```
