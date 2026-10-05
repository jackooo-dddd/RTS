# `nonclairvoyant_readiness`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.readiness.nonclairvoyant_readiness`
- Lean: `Prosa.Analysis.Definitions.Readiness.nonclairvoyant_readiness`
- Certificate: `nonclairvoyant_readiness_correspondence`

## Official Rocq

```coq
nonclairvoyant_readiness :
forall {Job : JobType} {H : JobCost Job} {H0 : JobArrival Job} {PState : ProcessorState Job},
@JobReady Job PState H H0 -> Prop

nonclairvoyant_readiness is not universe polymorphic
Arguments nonclairvoyant_readiness {Job H H0 PState} ReadinessModel
nonclairvoyant_readiness is transparent
Expands to: Constant prosa.analysis.definitions.readiness.nonclairvoyant_readiness
Declared in library prosa.analysis.definitions.readiness, line 30, characters 13-37
@nonclairvoyant_readiness
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobArrival Job) (PState : ProcessorState Job),
       @JobReady Job PState H H0 -> Prop
```

Body:

```coq
nonclairvoyant_readiness =
fun (Job : JobType) (H : JobCost Job) (H0 : JobArrival Job) (PState : ProcessorState Job)
  (ReadinessModel : @JobReady Job PState H H0) =>
forall (sched sched' : @schedule Job PState) (j : Equality.sort Job) (h : instant),
@identical_prefix Job PState sched sched' h ->
forall t : nat,
is_true (t <= h) ->
@job_ready Job PState H H0 ReadinessModel sched j t = @job_ready Job PState H H0 ReadinessModel sched' j t
     : forall {Job : JobType} {H : JobCost Job} {H0 : JobArrival Job} {PState : ProcessorState Job},
       @JobReady Job PState H H0 -> Prop

Arguments nonclairvoyant_readiness {Job H H0 PState} ReadinessModel
```

## Lean

```lean
@Prosa.Analysis.Definitions.Readiness.nonclairvoyant_readiness : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobCost Job] →
      [inst_2 : Prosa.Behavior.Job.JobArrival Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} → Prosa.Behavior.Ready.JobReady Job PState → Prop
```

Body:

```lean
def Prosa.Analysis.Definitions.Readiness.nonclairvoyant_readiness.{u_1, u_2, u_3} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [inst_1 : Prosa.Behavior.Job.JobCost Job] →
      [inst_2 : Prosa.Behavior.Job.JobArrival Job] →
        {PState : Prosa.Behavior.Schedule.ProcessorState Job} → Prosa.Behavior.Ready.JobReady Job PState → Prop :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobCost Job] [Prosa.Behavior.Job.JobArrival Job] {PState}
    ReadinessModel =>
  ∀ (sched sched' : Prosa.Behavior.Schedule.schedule PState) (j : Job) (h : Prosa.Behavior.Time.instant),
    Prosa.Analysis.Definitions.SchedulePrefix.identical_prefix sched sched' h →
      ∀ t ≤ h, Prosa.Behavior.Ready.job_ready sched j t = Prosa.Behavior.Ready.job_ready sched' j t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Readiness_nonclairvoyant_readiness
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Ready_JobReady Job
         inst_3 PState
         inst_6
         inst_9 ->
       SProp
```

Body:

```coq
Prosa_Analysis_Definitions_Readiness_nonclairvoyant_readiness@{u_1 u_2 u_3 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.max__u_1+1_u_2+2_u_3+2.0 Lean.u_2+1.0 Lean.u_3+1.0 Lean.u_1+2.0 Lean.u_3+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobCost Job
                                                                                inst_3)
  (inst_9 : Prosa_Behavior_Job_JobArrival
                                                                                Job
                                                                                inst_3)
  (PState : Prosa_Behavior_Schedule_ProcessorState Job
              inst_3)
  (ReadinessModel : Prosa_Behavior_Ready_JobReady Job
                      inst_3 PState
                      inst_6
                      inst_9) =>
forall
  (sched
   sched' : Prosa_Behavior_Schedule_schedule Job
              inst_3 PState)
  (j : Job) (h : Prosa_Behavior_Time_instant),
Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix Job
  inst_3 PState sched sched' h ->
forall t : Prosa_Behavior_Time_instant,
LE_le_inst1 Prosa_Behavior_Time_instant instLENat t h ->
@eq Bool
  (Prosa_Behavior_Ready_JobReady_job_ready Job
     inst_3 PState
     inst_6
     inst_9 ReadinessModel sched j t)
  (Prosa_Behavior_Ready_JobReady_job_ready Job
     inst_3 PState
     inst_6
     inst_9 ReadinessModel sched' j t)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Behavior_Ready_JobReady Job
         inst_3 PState
         inst_6
         inst_9 ->
       SProp

Arguments Prosa_Analysis_Definitions_Readiness_nonclairvoyant_readiness Job
  inst_3
  inst_6
  inst_9 PState 
  ReadinessModel
```
