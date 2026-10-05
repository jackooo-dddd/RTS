# `quiet_time`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.abstract.definitions.quiet_time`
- Lean: `Prosa.Analysis.Abstract.Definitions.quiet_time`
- Certificate: `ad_quiet_time_correspondence`

## Official Rocq

```coq
quiet_time :
forall {Job : JobType},
JobArrival Job ->
JobCost Job ->
forall {PState : ProcessorState Job},
@schedule Job PState -> Interference Job -> InterferingWorkload Job -> Equality.sort Job -> instant -> bool

quiet_time is not universe polymorphic
Arguments quiet_time {Job H0 H1 PState} sched {H2 H3} j t
quiet_time is transparent
Expands to: Constant prosa.analysis.abstract.definitions.quiet_time
Declared in library prosa.analysis.abstract.definitions, line 140, characters 13-23
@quiet_time
     : forall Job : JobType,
       JobArrival Job ->
       JobCost Job ->
       forall PState : ProcessorState Job,
       @schedule Job PState ->
       Interference Job -> InterferingWorkload Job -> Equality.sort Job -> instant -> bool
```

Body:

```coq
quiet_time =
fun (Job : JobType) (H0 : JobArrival Job) (H1 : JobCost Job) (PState : ProcessorState Job)
  (sched : @schedule Job PState) (H2 : Interference Job) (H3 : InterferingWorkload Job)
  (j : Equality.sort Job) (t : instant) =>
(@cumulative_interference Job H2 j 0 t == @cumulative_interfering_workload Job H3 j 0 t) &&
~~ @pending_earlier_and_at Job PState sched H1 H0 j t
     : forall {Job : JobType},
       JobArrival Job ->
       JobCost Job ->
       forall {PState : ProcessorState Job},
       @schedule Job PState ->
       Interference Job -> InterferingWorkload Job -> Equality.sort Job -> instant -> bool

Arguments quiet_time {Job H0 H1 PState} sched {H2 H3} j t
```

## Lean

```lean
@Prosa.Analysis.Abstract.Definitions.quiet_time : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Analysis.Abstract.Definitions.Interference Job] →
      [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] →
        [Prosa.Behavior.Job.JobArrival Job] →
          [Prosa.Behavior.Job.JobCost Job] →
            {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
              Prosa.Behavior.Schedule.schedule PState → Job → Prosa.Behavior.Time.instant → Bool
def Prosa.Analysis.Abstract.Definitions.quiet_time.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Analysis.Abstract.Definitions.Interference Job] →
      [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] →
        [Prosa.Behavior.Job.JobArrival Job] →
          [Prosa.Behavior.Job.JobCost Job] →
            {PState : Prosa.Behavior.Schedule.ProcessorState Job} →
              Prosa.Behavior.Schedule.schedule PState → Job → Prosa.Behavior.Time.instant → Bool :=
fun {Job} [DecidableEq Job] [Prosa.Analysis.Abstract.Definitions.Interference Job]
    [Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job] [Prosa.Behavior.Job.JobArrival Job]
    [Prosa.Behavior.Job.JobCost Job] {PState} sched j t =>
  decide
      (Prosa.Analysis.Abstract.Definitions.cumulative_interference j 0 t =
        Prosa.Analysis.Abstract.Definitions.cumulative_interfering_workload j 0 t) &&
    !Prosa.Behavior.Service.pending_earlier_and_at sched j t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_Definitions_quiet_time
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job -> Prosa_Behavior_Time_instant -> Bool
```

Body:

```coq
Prosa_Analysis_Abstract_Definitions_quiet_time@{u_1 u_2 u_3 Lean.u_1+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0
Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Analysis_Abstract_Definitions_Interference
                                                                                Job
                                                                                inst_3)
  (inst_9 : Prosa_Analysis_Abstract_Definitions_InterferingWorkload
                                                                                Job
                                                                                inst_3)
  (inst_12 : Prosa_Behavior_Job_JobArrival
                                                                                Job
                                                                                inst_3)
  (inst_15 : Prosa_Behavior_Job_JobCost Job
                                                                                inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (sched : Prosa_Behavior_Schedule_schedule Job
             inst_3 PState)
  (j : Job) (t : Prosa_Behavior_Time_instant) =>
Bool_and
  (Decidable_decide
     (@eq Nat
        (Prosa_Analysis_Abstract_Definitions_cumulative_interference Job
           inst_3
           inst_6 j
           (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0)) t)
        (Prosa_Analysis_Abstract_Definitions_cumulative_interfering_workload Job
           inst_3
           inst_9 j
           (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0)) t))
     (instDecidableEqNat
        (Prosa_Analysis_Abstract_Definitions_cumulative_interference Job
           inst_3
           inst_6 j
           (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0)) t)
        (Prosa_Analysis_Abstract_Definitions_cumulative_interfering_workload Job
           inst_3
           inst_9 j
           (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0)) t)))
  (Bool_not
     (Prosa_Behavior_Service_pending_earlier_and_at Job
        inst_3 PState sched
        inst_15
        inst_12 j t))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Analysis_Abstract_Definitions_Interference Job
         inst_3 ->
       Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
         inst_3 ->
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Job_JobCost Job
         inst_3 ->
       forall
         PState : Prosa_Behavior_Schedule_ProcessorState Job
                    inst_3,
       Prosa_Behavior_Schedule_schedule Job
         inst_3 PState ->
       Job -> Prosa_Behavior_Time_instant -> Bool

Arguments Prosa_Analysis_Abstract_Definitions_quiet_time Job
  inst_3
  inst_6
  inst_9
  inst_12
  inst_15 PState 
  sched j a____at____internal__hyg0
```
