# `arm_sbf_valid`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.sbf.average.arm_sbf_valid`
- Lean: `Prosa.Analysis.Facts.Model.Sbf.Average.arm_sbf_valid`
- Certificate: `arm_sbf_valid_correspondence`

## Official Rocq

```coq
arm_sbf_valid :
forall {Job : JobType} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job PState) (Π Θ ν : duration),
@average_resource_model Job PState Π Θ ν sched ->
@valid_supply_bound_function Job PState arr_seq sched (arm_sbf Π Θ ν)

arm_sbf_valid is not universe polymorphic
Arguments arm_sbf_valid {Job PState} arr_seq sched Π Θ ν H_average_resource_model
arm_sbf_valid is opaque
Expands to: Constant prosa.analysis.facts.model.sbf.average.arm_sbf_valid
Declared in library prosa.analysis.facts.model.sbf.average, line 70, characters 8-21
@arm_sbf_valid
     : forall (Job : JobType) (PState : ProcessorState Job) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job PState) (Π Θ ν : duration),
       @average_resource_model Job PState Π Θ ν sched ->
       @valid_supply_bound_function Job PState arr_seq sched (arm_sbf Π Θ ν)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Sbf.Average.arm_sbf_valid : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule PState) (period alloc delay : Prosa.Behavior.Time.duration),
  Prosa.Analysis.Definitions.Sbf.Average.average_resource_model period alloc delay sched →
    Prosa.Analysis.Definitions.Sbf.Plain.valid_supply_bound_function arr_seq sched
      (Prosa.Analysis.Definitions.Sbf.Average.arm_sbf period alloc delay)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Sbf_Average_arm_sbf_valid
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (period alloc delay : Prosa_Behavior_Time_duration),
       Prosa_Analysis_Definitions_Sbf_Average_average_resource_model Job
         inst_3 PState period alloc delay
         sched ->
       Prosa_Analysis_Definitions_Sbf_Plain_valid_supply_bound_function Job
         inst_3 PState arr_seq sched
         (Prosa_Analysis_Definitions_Sbf_Average_arm_sbf period alloc delay)
```
