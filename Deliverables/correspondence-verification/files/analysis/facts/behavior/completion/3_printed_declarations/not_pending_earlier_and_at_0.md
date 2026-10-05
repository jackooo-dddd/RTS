# `not_pending_earlier_and_at_0`

- Kind (Rocq): Remark
- Rocq: `prosa.analysis.facts.behavior.completion.not_pending_earlier_and_at_0`
- Lean: `Prosa.Analysis.Facts.Behavior.Completion.not_pending_earlier_and_at_0`
- Certificate: `not_pending_earlier_and_at_0_correspondence`

## Official Rocq

```coq
not_pending_earlier_and_at_0 :
forall {Job : JobType} {H : JobCost Job} {H0 : JobArrival Job} {PState : ProcessorState Job}
  (sched : @schedule Job PState) (j : Equality.sort Job),
is_true (~~ @pending_earlier_and_at Job PState sched H H0 j 0)

not_pending_earlier_and_at_0 is not universe polymorphic
Arguments not_pending_earlier_and_at_0 {Job H H0 PState} sched j
not_pending_earlier_and_at_0 is opaque
Expands to: Constant prosa.analysis.facts.behavior.completion.not_pending_earlier_and_at_0
Declared in library prosa.analysis.facts.behavior.completion, line 166, characters 9-37
@not_pending_earlier_and_at_0
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobArrival Job) (PState : ProcessorState Job)
         (sched : @schedule Job PState) (j : Equality.sort Job),
       is_true (~~ @pending_earlier_and_at Job PState sched H H0 j 0)
```

## Lean

```lean
@Prosa.Analysis.Facts.Behavior.Completion.not_pending_earlier_and_at_0 : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobArrival Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState) (j : Job),
  (!Prosa.Behavior.Service.pending_earlier_and_at sched j 0) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Behavior_Completion_not_pending_earlier_and_at_0
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (j : Job),
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_pending_earlier_and_at Job
               inst_3 PState sched
               inst_6
               inst_9 j
               (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 0 (instOfNatNat 0))))
         Bool_true
```
