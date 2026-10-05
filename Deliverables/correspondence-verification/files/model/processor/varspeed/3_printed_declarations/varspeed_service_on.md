# `varspeed_service_on`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.varspeed.varspeed_service_on`
- Lean: `Prosa.Model.Processor.Varspeed.varspeed_service_on`
- Certificate: `vs_service_on_correspondence`

## Official Rocq

```coq
varspeed_service_on : forall Job : JobType, Equality.sort Job -> processor_state Job -> unit -> work

varspeed_service_on is not universe polymorphic
Arguments varspeed_service_on Job j s _
varspeed_service_on is transparent
Expands to: Constant prosa.model.processor.varspeed.varspeed_service_on
Declared in library prosa.model.processor.varspeed, line 50, characters 15-34
varspeed_service_on
     : forall Job : JobType, Equality.sort Job -> processor_state Job -> unit -> work
```

Body:

```coq
varspeed_service_on =
fun (Job : JobType) (j : Equality.sort Job) (s : processor_state Job) =>
fun=> match s with
      | @Idle _ _ => 0
      | @Progress _ j' speed => if j' == j then speed else 0
      end
     : forall Job : JobType, Equality.sort Job -> processor_state Job -> unit -> work

Arguments varspeed_service_on Job j s _
```

## Lean

```lean
@Prosa.Model.Processor.Varspeed.varspeed_service_on : {Job : Prosa.Behavior.Job.JobType} →
  [DecidableEq Job] → Job → Prosa.Model.Processor.Varspeed.processor_state Job → Unit → Prosa.Behavior.Job.work
def Prosa.Model.Processor.Varspeed.varspeed_service_on.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [DecidableEq Job] → Job → Prosa.Model.Processor.Varspeed.processor_state Job → Unit → Prosa.Behavior.Job.work :=
fun {Job} [DecidableEq Job] j s x =>
  match s with
  | Prosa.Model.Processor.Varspeed.processor_state.Idle speed => 0
  | Prosa.Model.Processor.Varspeed.processor_state.Progress j' speed => if decide (j' = j) = true then speed else 0
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_Varspeed_varspeed_service_on
     : forall Job : Prosa_Behavior_Job_JobType,
       DecidableEq Job ->
       Job -> Prosa_Model_Processor_Varspeed_processor_state Job -> Unit -> Prosa_Behavior_Job_work
```

Body:

```coq
Prosa_Model_Processor_Varspeed_varspeed_service_on@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job) 
  (j : Job) (s : Prosa_Model_Processor_Varspeed_processor_state Job) (_ : Unit) =>
Prosa_Model_Processor_Varspeed_varspeed_scheduled_on_match_1 Job
  (fun _ : Prosa_Model_Processor_Varspeed_processor_state Job => Prosa_Behavior_Job_work) s
  (fun _ : Nat => OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
  (fun (j' : Job) (speed : Nat) =>
   ite Prosa_Behavior_Job_work
     (@eq Bool
        (Decidable_decide (@eq Job j' j)
           (inst_3 j' j))
        Bool_true)
     (instDecidableEqBool
        (Decidable_decide (@eq Job j' j)
           (inst_3 j' j))
        Bool_true)
     speed (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0)))
     : forall Job : Prosa_Behavior_Job_JobType,
       DecidableEq Job ->
       Job -> Prosa_Model_Processor_Varspeed_processor_state Job -> Unit -> Prosa_Behavior_Job_work

Arguments Prosa_Model_Processor_Varspeed_varspeed_service_on Job
  inst_3 j s
  x____at___Prosa_Model_Processor_Varspeed3103343038__hygCtx__hyg8
```
