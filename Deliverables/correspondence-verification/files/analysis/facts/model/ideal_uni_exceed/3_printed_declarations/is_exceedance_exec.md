# `is_exceedance_exec`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.facts.model.ideal_uni_exceed.is_exceedance_exec`
- Lean: `Prosa.Analysis.Facts.Model.IdealUniExceed.is_exceedance_exec`
- Certificate: `facts_is_exceedance_exec_correspondence`

## Official Rocq

```coq
is_exceedance_exec : forall {Job : JobType}, @State Job (ideal_uni_exceed.exceedance_proc_state Job) -> bool

is_exceedance_exec is not universe polymorphic
Arguments is_exceedance_exec {Job} pstate
is_exceedance_exec is transparent
Expands to: Constant prosa.analysis.facts.model.ideal_uni_exceed.is_exceedance_exec
Declared in library prosa.analysis.facts.model.ideal_uni_exceed, line 91, characters 13-31
@is_exceedance_exec
     : forall Job : JobType, @State Job (ideal_uni_exceed.exceedance_proc_state Job) -> bool
```

Body:

```coq
is_exceedance_exec =
fun (Job : JobType) (pstate : @State Job (ideal_uni_exceed.exceedance_proc_state Job)) =>
match pstate with
| @ideal_uni_exceed.ExceedanceExecution _ _ => true
| _ => false
end
     : forall {Job : JobType}, @State Job (ideal_uni_exceed.exceedance_proc_state Job) -> bool

Arguments is_exceedance_exec {Job} pstate
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.IdealUniExceed.is_exceedance_exec : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → Prosa.Behavior.Schedule.ProcessorState.State Job → Bool
def Prosa.Analysis.Facts.Model.IdealUniExceed.is_exceedance_exec.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → Prosa.Behavior.Schedule.ProcessorState.State Job → Bool :=
fun {Job} [DecidableEq Job] pstate =>
  match pstate with
  | Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state.ExceedanceExecution j => true
  | x => false
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_IdealUniExceed_is_exceedance_exec
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
         inst_3
         (Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state Job
            inst_3) ->
       Bool
```

Body:

```coq
Prosa_Analysis_Facts_Model_IdealUniExceed_is_exceedance_exec@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (pstate : Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
              inst_3
              (Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state Job
                 inst_3)) =>
Prosa_Analysis_Facts_Model_IdealUniExceed_is_exceedance_exec_match_1 Job
  inst_3
  (fun
     _ : Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
           inst_3
           (Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state Job
              inst_3) =>
   Bool)
  pstate (fun _ : Job => Bool_true)
  (fun
     _ : Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
           inst_3
           (Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state Job
              inst_3) =>
   Bool_false)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
         inst_3
         (Prosa_Model_Processor_IdealUniExceed_exceedance_proc_state Job
            inst_3) ->
       Bool

Arguments Prosa_Analysis_Facts_Model_IdealUniExceed_is_exceedance_exec Job
  inst_3 
  pstate
```
