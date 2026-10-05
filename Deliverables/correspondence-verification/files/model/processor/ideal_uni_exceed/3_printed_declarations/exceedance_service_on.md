# `exceedance_service_on`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.ideal_uni_exceed.exceedance_service_on`
- Lean: `Prosa.Model.Processor.IdealUniExceed.exceedance_service_on`
- Certificate: `iue_service_on_correspondence`

## Official Rocq

```coq
exceedance_service_on :
forall {Job : JobType}, Equality.sort Job -> @exceedance_processor_state Job -> unit -> work

exceedance_service_on is not universe polymorphic
Arguments exceedance_service_on {Job} j proc_state _
exceedance_service_on is transparent
Expands to: Constant prosa.model.processor.ideal_uni_exceed.exceedance_service_on
Declared in library prosa.model.processor.ideal_uni_exceed, line 83, characters 15-36
@exceedance_service_on
     : forall Job : JobType, Equality.sort Job -> @exceedance_processor_state Job -> unit -> work
```

Body:

```coq
exceedance_service_on =
fun (Job : JobType) (j : Equality.sort Job) (proc_state : @exceedance_processor_state Job) =>
fun=> match proc_state with
      | @NominalExecution _ j' => nat_of_bool (j' == j)
      | _ => 0
      end
     : forall {Job : JobType}, Equality.sort Job -> @exceedance_processor_state Job -> unit -> work

Arguments exceedance_service_on {Job} j proc_state _
```

## Lean

```lean
@Prosa.Model.Processor.IdealUniExceed.exceedance_service_on : {Job : Prosa.Behavior.Job.JobType} →
  [DecidableEq Job] →
    Job → Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state Job → Unit → Prosa.Behavior.Job.work
def Prosa.Model.Processor.IdealUniExceed.exceedance_service_on.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [DecidableEq Job] →
    Job → Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state Job → Unit → Prosa.Behavior.Job.work :=
fun {Job} [DecidableEq Job] j proc_state x =>
  match proc_state with
  | Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state.NominalExecution j' =>
    if decide (j' = j) = true then 1 else 0
  | Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state.ExceedanceExecution j => 0
  | Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state.Idle => 0
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_IdealUniExceed_exceedance_service_on
     : forall Job : Prosa_Behavior_Job_JobType,
       DecidableEq Job ->
       Job ->
       Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state Job -> Unit -> Prosa_Behavior_Job_work
```

Body:

```coq
Prosa_Model_Processor_IdealUniExceed_exceedance_service_on@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job) 
  (j : Job) (proc_state : Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state Job) 
  (_ : Unit) =>
Prosa_Model_Processor_IdealUniExceed_exceedance_scheduled_on_match_1 Job
  (fun _ : Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state Job => Prosa_Behavior_Job_work)
  proc_state
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
  (fun _ : Job => OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
  (fun _ : Unit => OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
     : forall Job : Prosa_Behavior_Job_JobType,
       DecidableEq Job ->
       Job ->
       Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state Job -> Unit -> Prosa_Behavior_Job_work

Arguments Prosa_Model_Processor_IdealUniExceed_exceedance_service_on Job
  inst_3 j proc_state
  x____at___Prosa_Model_Processor_IdealUniExceed1953532484__hygCtx__hyg8
```
