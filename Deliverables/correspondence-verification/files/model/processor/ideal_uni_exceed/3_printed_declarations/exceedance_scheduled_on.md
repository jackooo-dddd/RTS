# `exceedance_scheduled_on`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.ideal_uni_exceed.exceedance_scheduled_on`
- Lean: `Prosa.Model.Processor.IdealUniExceed.exceedance_scheduled_on`
- Certificate: `iue_scheduled_on_correspondence`

## Official Rocq

```coq
exceedance_scheduled_on :
forall {Job : JobType}, Equality.sort Job -> @exceedance_processor_state Job -> unit -> bool

exceedance_scheduled_on is not universe polymorphic
Arguments exceedance_scheduled_on {Job} j proc_state _
exceedance_scheduled_on is transparent
Expands to: Constant prosa.model.processor.ideal_uni_exceed.exceedance_scheduled_on
Declared in library prosa.model.processor.ideal_uni_exceed, line 58, characters 15-38
@exceedance_scheduled_on
     : forall Job : JobType, Equality.sort Job -> @exceedance_processor_state Job -> unit -> bool
```

Body:

```coq
exceedance_scheduled_on =
fun (Job : JobType) (j : Equality.sort Job) (proc_state : @exceedance_processor_state Job) =>
fun=> match proc_state with
      | @NominalExecution _ j' | @ExceedanceExecution _ j' => j' == j
      | @Idle _ => false
      end
     : forall {Job : JobType}, Equality.sort Job -> @exceedance_processor_state Job -> unit -> bool

Arguments exceedance_scheduled_on {Job} j proc_state _
```

## Lean

```lean
@Prosa.Model.Processor.IdealUniExceed.exceedance_scheduled_on : {Job : Prosa.Behavior.Job.JobType} →
  [DecidableEq Job] → Job → Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state Job → Unit → Bool
def Prosa.Model.Processor.IdealUniExceed.exceedance_scheduled_on.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [DecidableEq Job] → Job → Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state Job → Unit → Bool :=
fun {Job} [DecidableEq Job] j proc_state x =>
  match proc_state with
  | Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state.NominalExecution j' => decide (j' = j)
  | Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state.ExceedanceExecution j' => decide (j' = j)
  | Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state.Idle => false
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_IdealUniExceed_exceedance_scheduled_on
     : forall Job : Prosa_Behavior_Job_JobType,
       DecidableEq Job ->
       Job -> Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state Job -> Unit -> Bool
```

Body:

```coq
Prosa_Model_Processor_IdealUniExceed_exceedance_scheduled_on@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job) 
  (j : Job) (proc_state : Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state Job) 
  (_ : Unit) =>
Prosa_Model_Processor_IdealUniExceed_exceedance_scheduled_on_match_1 Job
  (fun _ : Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state Job => Bool) proc_state
  (fun j' : Job =>
   Decidable_decide (@eq Job j' j)
     (inst_3 j' j))
  (fun j' : Job =>
   Decidable_decide (@eq Job j' j)
     (inst_3 j' j))
  (fun _ : Unit => Bool_false)
     : forall Job : Prosa_Behavior_Job_JobType,
       DecidableEq Job ->
       Job -> Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state Job -> Unit -> Bool

Arguments Prosa_Model_Processor_IdealUniExceed_exceedance_scheduled_on Job
  inst_3 j proc_state
  x____at___Prosa_Model_Processor_IdealUniExceed1862607287__hygCtx__hyg9
```
