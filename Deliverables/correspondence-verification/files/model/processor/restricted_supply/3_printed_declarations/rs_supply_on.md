# `rs_supply_on`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.restricted_supply.rs_supply_on`
- Lean: `Prosa.Model.Processor.RestrictedSupply.rs_supply_on`
- Certificate: `rs_supply_on_correspondence`

## Official Rocq

```coq
rs_supply_on : forall Job : JobType, @processor_state Job -> work

rs_supply_on is not universe polymorphic
Arguments rs_supply_on Job s
rs_supply_on is transparent
Expands to: Constant prosa.model.processor.restricted_supply.rs_supply_on
Declared in library prosa.model.processor.restricted_supply, line 48, characters 15-27
rs_supply_on
     : forall Job : JobType, @processor_state Job -> work
```

Body:

```coq
rs_supply_on =
fun (Job : JobType) (s : @processor_state Job) => match s with
                                                  | @Idle _ | @Active _ _ => 1
                                                  | _ => 0
                                                  end
     : forall Job : JobType, @processor_state Job -> work

Arguments rs_supply_on Job s
```

## Lean

```lean
@Prosa.Model.Processor.RestrictedSupply.rs_supply_on : {Job : Prosa.Behavior.Job.JobType} →
  [DecidableEq Job] → Prosa.Model.Processor.RestrictedSupply.processor_state Job → Prosa.Behavior.Job.work
def Prosa.Model.Processor.RestrictedSupply.rs_supply_on.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [DecidableEq Job] → Prosa.Model.Processor.RestrictedSupply.processor_state Job → Prosa.Behavior.Job.work :=
fun {Job} [DecidableEq Job] s =>
  match s with
  | Prosa.Model.Processor.RestrictedSupply.processor_state.Idle => 1
  | Prosa.Model.Processor.RestrictedSupply.processor_state.Active j => 1
  | Prosa.Model.Processor.RestrictedSupply.processor_state.Unavailable j => 0
  | Prosa.Model.Processor.RestrictedSupply.processor_state.Inactive => 0
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_RestrictedSupply_rs_supply_on
     : forall Job : Prosa_Behavior_Job_JobType,
       DecidableEq Job ->
       Prosa_Model_Processor_RestrictedSupply_processor_state Job -> Prosa_Behavior_Job_work
```

Body:

```coq
Prosa_Model_Processor_RestrictedSupply_rs_supply_on@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType) (_ : DecidableEq Job)
  (s : Prosa_Model_Processor_RestrictedSupply_processor_state Job) =>
Prosa_Model_Processor_RestrictedSupply_rs_supply_on_match_1 Job
  (fun _ : Prosa_Model_Processor_RestrictedSupply_processor_state Job => Prosa_Behavior_Job_work) s
  (fun _ : Unit => OfNat_ofNat_inst1 Prosa_Behavior_Job_work 1 (instOfNatNat 1))
  (fun _ : Job => OfNat_ofNat_inst1 Prosa_Behavior_Job_work 1 (instOfNatNat 1))
  (fun _ : Job => OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
  (fun _ : Unit => OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
     : forall Job : Prosa_Behavior_Job_JobType,
       DecidableEq Job ->
       Prosa_Model_Processor_RestrictedSupply_processor_state Job -> Prosa_Behavior_Job_work

Arguments Prosa_Model_Processor_RestrictedSupply_rs_supply_on Job
  inst_3 s
```
