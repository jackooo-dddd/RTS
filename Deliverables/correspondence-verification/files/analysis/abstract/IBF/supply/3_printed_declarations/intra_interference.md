# `intra_interference`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.abstract.IBF.supply.intra_interference`
- Lean: `Prosa.Analysis.Abstract.IBF.Supply.intra_interference`
- Certificate: `intra_interference_correspondence`

## Official Rocq

```coq
intra_interference :
forall {Job : JobType} {PState : ProcessorState Job},
@schedule Job PState -> Interference Job -> Equality.sort Job -> instant -> bool

intra_interference is not universe polymorphic
Arguments intra_interference {Job PState} sched {H2} j t
intra_interference is transparent
Expands to: Constant prosa.analysis.abstract.IBF.supply.intra_interference
Declared in library prosa.analysis.abstract.IBF.supply, line 54, characters 13-31
@intra_interference
     : forall (Job : JobType) (PState : ProcessorState Job),
       @schedule Job PState -> Interference Job -> Equality.sort Job -> instant -> bool
```

Body:

```coq
intra_interference =
fun (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
  (H2 : Interference Job) (j : Equality.sort Job) =>
     : forall {Job : JobType} {PState : ProcessorState Job},
       @schedule Job PState -> Interference Job -> Equality.sort Job -> instant -> bool

Arguments intra_interference {Job PState} sched {H2} j t
```

## Lean

```lean
@Prosa.Analysis.Abstract.IBF.Supply.intra_interference : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState →
        [Prosa.Analysis.Abstract.Definitions.Interference Job] → Job → Prosa.Behavior.Time.instant → Bool
```

Body:

```lean
def Prosa.Analysis.Abstract.IBF.Supply.intra_interference.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
      Prosa.Behavior.Schedule.schedule PState →
        [Prosa.Analysis.Abstract.Definitions.Interference Job] → Job → Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] {PState} sched [Prosa.Analysis.Abstract.Definitions.Interference Job] j t =>
  Prosa.Analysis.Abstract.Definitions.cond_interference (fun x t => Prosa.Model.Processor.Supply.has_supply sched t) j t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_IBF_Supply_intra_interference
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Analysis_Abstract_IBF_Supply_intra_interference@{u_1 u_2 u_3 Lean.u_1+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0
Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (inst_10 : Prosa_Analysis_Abstract_Definitions_Interference
                                                                               Job
                                                                               inst_3)
  (j : Job) (t : Prosa_Behavior_Time_instant) =>
Prosa_Analysis_Abstract_Definitions_cond_interference Job
  inst_3
  inst_10
  (fun (_ : Job) (t0 : Prosa_Behavior_Time_instant) =>
   Prosa_Model_Processor_Supply_has_supply Job
     inst_3 PState sched t0)
  j t
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       Job -> Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Analysis_Abstract_IBF_Supply_intra_interference Job
  inst_3 PState sched
  inst_10 j t
```
