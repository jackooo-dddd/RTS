# `basic_ready_instance`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.EDF.preemptive_sched.basic_ready_instance`
- Lean: `Prosa.Implementation.Refinements.EDF.PreemptiveSched.basic_ready_instance`
- Certificate: `basic_ready_instance_correspondence`

## Official Rocq

```coq
basic_ready_instance : @JobReady Job (processor_state Job) task.JobCost task.JobArrival

basic_ready_instance is not universe polymorphic
basic_ready_instance is transparent
Expands to: Constant prosa.implementation.refinements.EDF.preemptive_sched.basic_ready_instance
Declared in library prosa.implementation.refinements.EDF.preemptive_sched, line 28, characters 11-31
basic_ready_instance
     : @JobReady Job (processor_state Job) task.JobCost task.JobArrival
```

Body:

```coq
basic_ready_instance =
@basic.basic_ready_instance Job (processor_state Job) task.JobArrival task.JobCost
     : @JobReady Job (processor_state Job) task.JobCost task.JobArrival
```

## Lean

```lean
Prosa.Implementation.Refinements.EDF.PreemptiveSched.basic_ready_instance : Prosa.Behavior.Ready.JobReady
  Prosa.Implementation.Refinements.EDF.PreemptiveSched.Job
  (Prosa.Model.Processor.Ideal.processor_state Prosa.Implementation.Refinements.EDF.PreemptiveSched.Job)
```

Body:

```lean
@[instance_reducible] def Prosa.Implementation.Refinements.EDF.PreemptiveSched.basic_ready_instance : Prosa.Behavior.Ready.JobReady
  Prosa.Implementation.Refinements.EDF.PreemptiveSched.Job
  (Prosa.Model.Processor.Ideal.processor_state Prosa.Implementation.Refinements.EDF.PreemptiveSched.Job) :=
Prosa.Model.Readiness.Basic.basic_ready_instance
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_EDF_PreemptiveSched_basic_ready_instance
     : Prosa_Behavior_Ready_JobReady_inst7 Prosa_Implementation_Refinements_EDF_PreemptiveSched_Job
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
         (Prosa_Model_Processor_Ideal_processor_state_inst1
            Prosa_Implementation_Refinements_EDF_PreemptiveSched_Job
            Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job)
         Prosa_Implementation_Definitions_Task_JobCost Prosa_Implementation_Definitions_Task_JobArrival
```

Body:

```coq
Prosa_Implementation_Refinements_EDF_PreemptiveSched_basic_ready_instance@{} =
Prosa_Model_Readiness_Basic_basic_ready_instance_inst7
  Prosa_Implementation_Refinements_EDF_PreemptiveSched_Job
  Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
  (Prosa_Model_Processor_Ideal_processor_state_inst1 Prosa_Implementation_Refinements_EDF_PreemptiveSched_Job
     Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job)
  Prosa_Implementation_Definitions_Task_JobArrival Prosa_Implementation_Definitions_Task_JobCost
     : Prosa_Behavior_Ready_JobReady_inst7 Prosa_Implementation_Refinements_EDF_PreemptiveSched_Job
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
         (Prosa_Model_Processor_Ideal_processor_state_inst1
            Prosa_Implementation_Refinements_EDF_PreemptiveSched_Job
            Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job)
         Prosa_Implementation_Definitions_Task_JobCost Prosa_Implementation_Definitions_Task_JobArrival
```
