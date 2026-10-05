# `prm_sbf_valid`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.sbf.periodic.prm_sbf_valid`
- Lean: `Prosa.Analysis.Facts.Model.Sbf.Periodic.prm_sbf_valid`
- Certificate: `prm_sbf_valid_correspondence`

## Official Rocq

```coq
prm_sbf_valid :
forall {Job : JobType} {PState : ProcessorState Job},
@unit_supply_proc_model Job PState ->
forall (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) (Π γ : duration),
@periodic_resource_model Job PState Π γ sched ->
@valid_supply_bound_function Job PState arr_seq sched (prm_sbf Π γ)

prm_sbf_valid is not universe polymorphic
Arguments prm_sbf_valid {Job PState} H_unit_supply_proc_model arr_seq sched Π γ H_periodic_resource_model
prm_sbf_valid is opaque
Expands to: Constant prosa.analysis.facts.model.sbf.periodic.prm_sbf_valid
Declared in library prosa.analysis.facts.model.sbf.periodic, line 368, characters 8-21
@prm_sbf_valid
     : forall (Job : JobType) (PState : ProcessorState Job),
       @unit_supply_proc_model Job PState ->
       forall (arr_seq : arrival_sequence Job) (sched : @schedule Job PState) (Π γ : duration),
       @periodic_resource_model Job PState Π γ sched ->
       @valid_supply_bound_function Job PState arr_seq sched (prm_sbf Π γ)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Sbf.Periodic.prm_sbf_valid : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.unit_supply_proc_model PState →
    ∀ (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState)
      (period alloc : Prosa.Behavior.Time.duration),
      Prosa.Analysis.Definitions.Sbf.Periodic.periodic_resource_model period alloc sched →
        Prosa.Analysis.Definitions.Sbf.Plain.valid_supply_bound_function arr_seq sched
          (Prosa.Analysis.Definitions.Sbf.Periodic.prm_sbf period alloc)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Sbf_Periodic_prm_sbf_valid
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3),
       Prosa_Model_Processor_PlatformProperties_unit_supply_proc_model Job
         inst_3 PState ->
       forall
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (period alloc : Prosa_Behavior_Time_duration),
       Prosa_Analysis_Definitions_Sbf_Periodic_periodic_resource_model Job
         inst_3 PState period alloc
         sched ->
       Prosa_Analysis_Definitions_Sbf_Plain_valid_supply_bound_function Job
         inst_3 PState arr_seq sched
         (Prosa_Analysis_Definitions_Sbf_Periodic_prm_sbf period alloc)
```
