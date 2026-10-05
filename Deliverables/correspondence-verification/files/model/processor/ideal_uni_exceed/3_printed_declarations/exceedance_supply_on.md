# `exceedance_supply_on`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.ideal_uni_exceed.exceedance_supply_on`
- Lean: `Prosa.Model.Processor.IdealUniExceed.exceedance_supply_on`
- Certificate: `iue_supply_on_correspondence`

## Official Rocq

```coq
exceedance_supply_on : forall {Job : JobType}, @exceedance_processor_state Job -> unit -> work

exceedance_supply_on is not universe polymorphic
Arguments exceedance_supply_on {Job} proc_state _
exceedance_supply_on is transparent
Expands to: Constant prosa.model.processor.ideal_uni_exceed.exceedance_supply_on
Declared in library prosa.model.processor.ideal_uni_exceed, line 72, characters 15-35
@exceedance_supply_on
     : forall Job : JobType, @exceedance_processor_state Job -> unit -> work
```

Body:

```coq
exceedance_supply_on =
fun (Job : JobType) (proc_state : @exceedance_processor_state Job) =>
fun=> match proc_state with
      | @ExceedanceExecution _ _ => 0
      | _ => 1
      end
     : forall {Job : JobType}, @exceedance_processor_state Job -> unit -> work

Arguments exceedance_supply_on {Job} proc_state _
```

## Lean

```lean
@Prosa.Model.Processor.IdealUniExceed.exceedance_supply_on : {Job : Prosa.Behavior.Job.JobType} →
  [DecidableEq Job] →
    Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state Job → Unit → Prosa.Behavior.Job.work
def Prosa.Model.Processor.IdealUniExceed.exceedance_supply_on.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [DecidableEq Job] →
    Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state Job → Unit → Prosa.Behavior.Job.work :=
fun {Job} [DecidableEq Job] proc_state x =>
  match proc_state with
  | Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state.NominalExecution j => 1
  | Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state.ExceedanceExecution j => 0
  | Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state.Idle => 1
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_IdealUniExceed_exceedance_supply_on
     : forall Job : Prosa_Behavior_Job_JobType,
       DecidableEq Job ->
       Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state Job -> Unit -> Prosa_Behavior_Job_work
```

Body:

```coq
Prosa_Model_Processor_IdealUniExceed_exceedance_supply_on@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType) (_ : DecidableEq Job)
  (proc_state : Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state Job) 
  (_ : Unit) =>
Prosa_Model_Processor_IdealUniExceed_exceedance_scheduled_on_match_1 Job
  (fun _ : Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state Job => Prosa_Behavior_Job_work)
  proc_state (fun _ : Job => OfNat_ofNat_inst1 Prosa_Behavior_Job_work 1 (instOfNatNat 1))
  (fun _ : Job => OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
  (fun _ : Unit => OfNat_ofNat_inst1 Prosa_Behavior_Job_work 1 (instOfNatNat 1))
     : forall Job : Prosa_Behavior_Job_JobType,
       DecidableEq Job ->
       Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state Job -> Unit -> Prosa_Behavior_Job_work

Arguments Prosa_Model_Processor_IdealUniExceed_exceedance_supply_on Job
  inst_3 proc_state
  x____at___Prosa_Model_Processor_IdealUniExceed1953532484__hygCtx__hyg8
```
