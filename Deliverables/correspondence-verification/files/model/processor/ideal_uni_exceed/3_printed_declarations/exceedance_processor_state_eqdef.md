# `exceedance_processor_state_eqdef`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.ideal_uni_exceed.exceedance_processor_state_eqdef`
- Lean: `Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state_eqdef`
- Certificate: `iue_eqdef_correspondence`

## Official Rocq

```coq
exceedance_processor_state_eqdef :
forall {Job : JobType}, @exceedance_processor_state Job -> @exceedance_processor_state Job -> bool

exceedance_processor_state_eqdef is not universe polymorphic
Arguments exceedance_processor_state_eqdef {Job} p1 p2
exceedance_processor_state_eqdef is transparent
Expands to: Constant prosa.model.processor.ideal_uni_exceed.exceedance_processor_state_eqdef
Declared in library prosa.model.processor.ideal_uni_exceed, line 25, characters 13-45
@exceedance_processor_state_eqdef
     : forall Job : JobType, @exceedance_processor_state Job -> @exceedance_processor_state Job -> bool
```

Body:

```coq
exceedance_processor_state_eqdef =
fun (Job : JobType) (p1 p2 : @exceedance_processor_state Job) =>
match p1 with
| @NominalExecution _ j1 => match p2 with
                            | @NominalExecution _ j2 => j1 == j2
                            | _ => false
                            end
| @ExceedanceExecution _ j1 => match p2 with
                               | @ExceedanceExecution _ j2 => j1 == j2
                               | _ => false
                               end
| @Idle _ => match p2 with
             | @Idle _ => true
             | _ => false
             end
end
     : forall {Job : JobType}, @exceedance_processor_state Job -> @exceedance_processor_state Job -> bool

Arguments exceedance_processor_state_eqdef {Job} p1 p2
```

## Lean

```lean
@Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state_eqdef : {Job : Prosa.Behavior.Job.JobType} →
  [DecidableEq Job] →
    Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state Job →
      Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state Job → Bool
def Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state_eqdef.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [DecidableEq Job] →
    Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state Job →
      Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state Job → Bool :=
fun {Job} [DecidableEq Job] p1 p2 =>
  match p1, p2 with
  | Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state.NominalExecution j1,
    Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state.NominalExecution j2 => decide (j1 = j2)
  | Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state.ExceedanceExecution j1,
    Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state.ExceedanceExecution j2 => decide (j1 = j2)
  | Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state.Idle,
    Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state.Idle => true
  | x, x_1 => false
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_eqdef
     : forall Job : Prosa_Behavior_Job_JobType,
       DecidableEq Job ->
       Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state Job ->
       Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state Job -> Bool
```

Body:

```coq
Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_eqdef@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (p1 p2 : Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state Job) =>
Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_eqdef_match_1 Job
  (fun _ _ : Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state Job => Bool) p1 p2
  (fun j1 j2 : Job =>
   Decidable_decide (@eq Job j1 j2)
     (inst_3 j1 j2))
  (fun j1 j2 : Job =>
   Decidable_decide (@eq Job j1 j2)
     (inst_3 j1 j2))
  (fun _ : Unit => Bool_true)
  (fun _ _ : Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state Job => Bool_false)
     : forall Job : Prosa_Behavior_Job_JobType,
       DecidableEq Job ->
       Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state Job ->
       Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state Job -> Bool

Arguments Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_eqdef Job
  inst_3 p1 p2
```
