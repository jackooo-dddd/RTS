# `eqn_exceedance_processor_state`

- Kind (Rocq): Lemma
- Rocq: `prosa.model.processor.ideal_uni_exceed.eqn_exceedance_processor_state`
- Lean: `Prosa.Model.Processor.IdealUniExceed.eqn_exceedance_processor_state`
- Certificate: `iue_eqn_statement_correspondence`

## Official Rocq

```coq
eqn_exceedance_processor_state :
forall {Job : JobType},
Equality.axiom (T:=@exceedance_processor_state Job) (@exceedance_processor_state_eqdef Job)

eqn_exceedance_processor_state is not universe polymorphic
Arguments eqn_exceedance_processor_state {Job} x y
eqn_exceedance_processor_state is opaque
Expands to: Constant prosa.model.processor.ideal_uni_exceed.eqn_exceedance_processor_state
Declared in library prosa.model.processor.ideal_uni_exceed, line 34, characters 8-38
@eqn_exceedance_processor_state
     : forall Job : JobType,
       Equality.axiom (T:=@exceedance_processor_state Job) (@exceedance_processor_state_eqdef Job)
```

## Lean

```lean
@Prosa.Model.Processor.IdealUniExceed.eqn_exceedance_processor_state : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    (p1 p2 : Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state Job) →
      Prosa.Model.Processor.IdealUniExceed.BoolReflect (p1 = p2)
        (Prosa.Model.Processor.IdealUniExceed.exceedance_processor_state_eqdef p1 p2)
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_IdealUniExceed_eqn_exceedance_processor_state
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (p1 p2 : Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state Job),
       Prosa_Model_Processor_IdealUniExceed_BoolReflect
         (@eq (Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state Job) p1 p2)
         (Prosa_Model_Processor_IdealUniExceed_exceedance_processor_state_eqdef Job
            inst_3 p1 p2)
```
