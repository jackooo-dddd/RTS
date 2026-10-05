# `rs_service_on`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.restricted_supply.rs_service_on`
- Lean: `Prosa.Model.Processor.RestrictedSupply.rs_service_on`
- Certificate: `rs_service_on_correspondence`

## Official Rocq

```coq
rs_service_on : forall Job : JobType, Equality.sort Job -> @processor_state Job -> work

rs_service_on is not universe polymorphic
Arguments rs_service_on Job j s
rs_service_on is transparent
Expands to: Constant prosa.model.processor.restricted_supply.rs_service_on
Declared in library prosa.model.processor.restricted_supply, line 56, characters 15-28
rs_service_on
     : forall Job : JobType, Equality.sort Job -> @processor_state Job -> work
```

Body:

```coq
rs_service_on =
fun (Job : JobType) (j : Equality.sort Job) (s : @processor_state Job) =>
match s with
| @Active _ j' => if j' == j then 1 else 0
| _ => 0
end
     : forall Job : JobType, Equality.sort Job -> @processor_state Job -> work

Arguments rs_service_on Job j s
```

## Lean

```lean
@Prosa.Model.Processor.RestrictedSupply.rs_service_on : {Job : Prosa.Behavior.Job.JobType} →
  [DecidableEq Job] → Job → Prosa.Model.Processor.RestrictedSupply.processor_state Job → Prosa.Behavior.Job.work
def Prosa.Model.Processor.RestrictedSupply.rs_service_on.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [DecidableEq Job] → Job → Prosa.Model.Processor.RestrictedSupply.processor_state Job → Prosa.Behavior.Job.work :=
fun {Job} [DecidableEq Job] j s =>
  match s with
  | Prosa.Model.Processor.RestrictedSupply.processor_state.Active j' => if decide (j' = j) = true then 1 else 0
  | Prosa.Model.Processor.RestrictedSupply.processor_state.Idle => 0
  | Prosa.Model.Processor.RestrictedSupply.processor_state.Unavailable j => 0
  | Prosa.Model.Processor.RestrictedSupply.processor_state.Inactive => 0
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_RestrictedSupply_rs_service_on
     : forall Job : Prosa_Behavior_Job_JobType,
       DecidableEq Job ->
       Job -> Prosa_Model_Processor_RestrictedSupply_processor_state Job -> Prosa_Behavior_Job_work
```

Body:

```coq
Prosa_Model_Processor_RestrictedSupply_rs_service_on@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job) 
  (j : Job) (s : Prosa_Model_Processor_RestrictedSupply_processor_state Job) =>
Prosa_Model_Processor_RestrictedSupply_rs_service_on_match_1 Job
  (fun _ : Prosa_Model_Processor_RestrictedSupply_processor_state Job => Prosa_Behavior_Job_work) s
  (fun j' : Job =>
   ite Prosa_Behavior_Job_work
     (@eq Bool
        (Decidable_decide (@eq Job j' j)
           (inst_3 j' j))
        Bool_true)
     (instDecidableEqBool
        (Decidable_decide (@eq Job j' j)
           (inst_3 j' j))
        Bool_true)
     (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 1 (instOfNatNat 1))
     (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0)))
  (fun _ : Unit => OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
  (fun _ : Job => OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
  (fun _ : Unit => OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
     : forall Job : Prosa_Behavior_Job_JobType,
       DecidableEq Job ->
       Job -> Prosa_Model_Processor_RestrictedSupply_processor_state Job -> Prosa_Behavior_Job_work

Arguments Prosa_Model_Processor_RestrictedSupply_rs_service_on Job
  inst_3 j s
```
