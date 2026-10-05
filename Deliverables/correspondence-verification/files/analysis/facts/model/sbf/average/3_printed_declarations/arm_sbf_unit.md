# `arm_sbf_unit`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.sbf.average.arm_sbf_unit`
- Lean: `Prosa.Analysis.Facts.Model.Sbf.Average.arm_sbf_unit`
- Certificate: `arm_sbf_unit_correspondence`

## Official Rocq

```coq
arm_sbf_unit :
forall {Job : JobType} {PState : ProcessorState Job} (sched : @schedule Job PState) (Π Θ ν : duration),
@average_resource_model Job PState Π Θ ν sched -> unit_supply_bound_function (arm_sbf Π Θ ν)

arm_sbf_unit is not universe polymorphic
Arguments arm_sbf_unit {Job PState} sched Π Θ ν H_average_resource_model δ
arm_sbf_unit is opaque
Expands to: Constant prosa.analysis.facts.model.sbf.average.arm_sbf_unit
Declared in library prosa.analysis.facts.model.sbf.average, line 49, characters 8-20
@arm_sbf_unit
     : forall (Job : JobType) (PState : ProcessorState Job) (sched : @schedule Job PState) (Π Θ ν : duration),
       @average_resource_model Job PState Π Θ ν sched -> unit_supply_bound_function (arm_sbf Π Θ ν)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Sbf.Average.arm_sbf_unit : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (sched : Prosa.Behavior.Schedule.schedule PState)
  (period alloc delay : Prosa.Behavior.Time.duration),
  Prosa.Analysis.Definitions.Sbf.Average.average_resource_model period alloc delay sched →
    Prosa.Analysis.Definitions.Sbf.Pred.unit_supply_bound_function
      (Prosa.Analysis.Definitions.Sbf.Average.arm_sbf period alloc delay)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Sbf_Average_arm_sbf_unit
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (period alloc delay : Prosa_Behavior_Time_duration),
       Prosa_Analysis_Definitions_Sbf_Average_average_resource_model Job
         inst_3 PState period alloc delay
         sched ->
       Prosa_Analysis_Definitions_Sbf_Pred_unit_supply_bound_function
         (Prosa_Analysis_Definitions_Sbf_Average_arm_sbf period alloc delay)
```
