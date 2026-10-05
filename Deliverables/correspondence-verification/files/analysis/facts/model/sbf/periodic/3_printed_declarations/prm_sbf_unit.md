# `prm_sbf_unit`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.sbf.periodic.prm_sbf_unit`
- Lean: `Prosa.Analysis.Facts.Model.Sbf.Periodic.prm_sbf_unit`
- Certificate: `prm_sbf_unit_correspondence`

## Official Rocq

```coq
prm_sbf_unit :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) (Π γ : duration),
@periodic_resource_model Job PState Π γ sched -> unit_supply_bound_function (prm_sbf Π γ)

prm_sbf_unit is not universe polymorphic
Arguments prm_sbf_unit {Job PState} sched Π γ H_periodic_resource_model δ
prm_sbf_unit is opaque
Expands to: Constant prosa.analysis.facts.model.sbf.periodic.prm_sbf_unit
Declared in library prosa.analysis.facts.model.sbf.periodic, line 89, characters 8-20
@prm_sbf_unit
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) (Π γ : duration),
       @periodic_resource_model Job PState Π γ sched -> unit_supply_bound_function (prm_sbf Π γ)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Sbf.Periodic.prm_sbf_unit : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState)
  (period alloc : Prosa.Behavior.Time.duration),
  Prosa.Analysis.Definitions.Sbf.Periodic.periodic_resource_model period alloc sched →
    Prosa.Analysis.Definitions.Sbf.Pred.unit_supply_bound_function
      (Prosa.Analysis.Definitions.Sbf.Periodic.prm_sbf period alloc)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Sbf_Periodic_prm_sbf_unit
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
       Prosa_Analysis_Definitions_Sbf_Pred_unit_supply_bound_function
         (Prosa_Analysis_Definitions_Sbf_Periodic_prm_sbf period alloc)
```
