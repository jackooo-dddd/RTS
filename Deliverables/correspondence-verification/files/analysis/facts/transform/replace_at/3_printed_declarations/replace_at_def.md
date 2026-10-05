# `replace_at_def`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.replace_at.replace_at_def`
- Lean: `Prosa.Analysis.Facts.Transform.ReplaceAt.replace_at_def`
- Certificate: `replace_at_def_correspondence`

## Official Rocq

```coq
replace_at_def :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) 
  (t' : instant) (nstate : @State Job PState),
@replace_at Job PState sched t' nstate t' = nstate

replace_at_def is not universe polymorphic
Arguments replace_at_def {Job PState} sched t' nstate
replace_at_def is opaque
Expands to: Constant prosa.analysis.facts.transform.replace_at.replace_at_def
Declared in library prosa.analysis.facts.transform.replace_at, line 29, characters 8-22
@replace_at_def
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) 
         (t' : instant) (nstate : @State Job PState),
       @replace_at Job PState sched t' nstate t' = nstate
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.ReplaceAt.replace_at_def : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState)
  (t' : Prosa.Behavior.Time.instant) (nstate : Prosa.Behavior.Schedule.ProcessorState.State Job),
  Prosa.Analysis.Transform.Swap.replace_at sched t' nstate t' = nstate
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_ReplaceAt_replace_at_def
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (t' : Prosa_Behavior_Time_instant)
         (nstate : Prosa_Behavior_Schedule_ProcessorState_State Job
                     inst_3 PState),
       @eq
         (Prosa_Behavior_Schedule_ProcessorState_State Job
            inst_3 PState)
         (Prosa_Analysis_Transform_Swap_replace_at Job
            inst_3 PState sched t'
            nstate t')
         nstate
```
