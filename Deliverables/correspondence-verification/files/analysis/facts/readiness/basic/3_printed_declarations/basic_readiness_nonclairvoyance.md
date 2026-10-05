# `basic_readiness_nonclairvoyance`

- Kind (Rocq): Fact
- Rocq: `prosa.analysis.facts.readiness.basic.basic_readiness_nonclairvoyance`
- Lean: `Prosa.Analysis.Facts.Readiness.Basic.basic_readiness_nonclairvoyance`
- Certificate: `basic_readiness_nonclairvoyance_correspondence`

## Official Rocq

```coq
basic_readiness_nonclairvoyance :
forall {Job : JobType} {PState : ProcessorState Job} {H : JobArrival Job} {H0 : JobCost Job},
@nonclairvoyant_readiness Job H0 H PState (@basic_ready_instance Job PState H H0)

basic_readiness_nonclairvoyance is not universe polymorphic
Arguments basic_readiness_nonclairvoyance {Job PState H H0} sched sched' j h _ t _
basic_readiness_nonclairvoyance is opaque
Expands to: Constant prosa.analysis.facts.readiness.basic.basic_readiness_nonclairvoyance
Declared in library prosa.analysis.facts.readiness.basic, line 22, characters 7-38
@basic_readiness_nonclairvoyance
     : forall (Job : JobType) (PState : ProcessorState Job) (H : JobArrival Job) (H0 : JobCost Job),
       @nonclairvoyant_readiness Job H0 H PState (@basic_ready_instance Job PState H H0)
```

## Lean

```lean
@Prosa.Analysis.Facts.Readiness.Basic.basic_readiness_nonclairvoyance : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job],
  Prosa.Analysis.Definitions.Readiness.nonclairvoyant_readiness Prosa.Model.Readiness.Basic.basic_ready_instance
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Readiness_Basic_basic_readiness_nonclairvoyance
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (inst_8 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_11 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3),
       Prosa_Analysis_Definitions_Readiness_nonclairvoyant_readiness Job
         inst_3
         inst_11
         inst_8 PState
         (Prosa_Model_Readiness_Basic_basic_ready_instance Job
            inst_3 PState
            inst_8
            inst_11)
```
