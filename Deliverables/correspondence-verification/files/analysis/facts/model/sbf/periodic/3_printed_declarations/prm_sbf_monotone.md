# `prm_sbf_monotone`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.sbf.periodic.prm_sbf_monotone`
- Lean: `Prosa.Analysis.Facts.Model.Sbf.Periodic.prm_sbf_monotone`
- Certificate: `prm_sbf_monotone_correspondence`

## Official Rocq

```coq
prm_sbf_monotone :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) (Π γ : duration),
@periodic_resource_model Job PState Π γ sched -> sbf_is_monotone (prm_sbf Π γ)

prm_sbf_monotone is not universe polymorphic
Arguments prm_sbf_monotone {Job PState} sched Π γ H_periodic_resource_model x y _
prm_sbf_monotone is opaque
Expands to: Constant prosa.analysis.facts.model.sbf.periodic.prm_sbf_monotone
Declared in library prosa.analysis.facts.model.sbf.periodic, line 45, characters 8-24
@prm_sbf_monotone
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) (Π γ : duration),
       @periodic_resource_model Job PState Π γ sched -> sbf_is_monotone (prm_sbf Π γ)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Sbf.Periodic.prm_sbf_monotone : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState) (period alloc : Prosa.Behavior.Time.duration),
  Prosa.Analysis.Definitions.Sbf.Periodic.periodic_resource_model period alloc sched →
    Prosa.Analysis.Definitions.Sbf.Pred.sbf_is_monotone (Prosa.Analysis.Definitions.Sbf.Periodic.prm_sbf period alloc)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Sbf_Periodic_prm_sbf_monotone
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (period alloc : Prosa_Behavior_Time_duration),
       Prosa_Analysis_Definitions_Sbf_Periodic_periodic_resource_model Job
         inst_3 PState period alloc
         sched ->
       Prosa_Analysis_Definitions_Sbf_Pred_sbf_is_monotone
         (Prosa_Analysis_Definitions_Sbf_Periodic_prm_sbf period alloc)
```
