# `sequential_ready_instance`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.FP.nonpreemptive_sched.sequential_ready_instance`
- Lean: `Prosa.Implementation.Refinements.FP.NonpreemptiveSched.sequential_ready_instance`
- Certificate: `sequential_ready_instance_correspondence`

## Official Rocq

```coq
sequential_ready_instance : arrival_sequence Job -> @JobReady Job (processor_state Job) JobCost JobArrival

sequential_ready_instance is not universe polymorphic
Arguments sequential_ready_instance arr_seq
sequential_ready_instance is transparent
Expands to: Constant prosa.implementation.refinements.FP.nonpreemptive_sched.sequential_ready_instance
Declared in library prosa.implementation.refinements.FP.nonpreemptive_sched, line 27, characters 11-36
sequential_ready_instance
     : arrival_sequence Job -> @JobReady Job (processor_state Job) JobCost JobArrival
```

Body:

```coq
sequential_ready_instance =
       (@reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality concrete_task) JobTask
       JobArrival JobCost (processor_state Job)]
     : arrival_sequence Job -> @JobReady Job (processor_state Job) JobCost JobArrival

Arguments sequential_ready_instance arr_seq
```

## Lean

```lean
Prosa.Implementation.Refinements.FP.NonpreemptiveSched.sequential_ready_instance : Prosa.Behavior.Arrival_sequence.arrival_sequence
    Prosa.Implementation.Refinements.FP.NonpreemptiveSched.Job →
  Prosa.Behavior.Ready.JobReady Prosa.Implementation.Refinements.FP.NonpreemptiveSched.Job
    (Prosa.Model.Processor.Ideal.processor_state Prosa.Implementation.Refinements.FP.NonpreemptiveSched.Job)
```

Body:

```lean
def Prosa.Implementation.Refinements.FP.NonpreemptiveSched.sequential_ready_instance : Prosa.Behavior.Arrival_sequence.arrival_sequence
    Prosa.Implementation.Refinements.FP.NonpreemptiveSched.Job →
  Prosa.Behavior.Ready.JobReady Prosa.Implementation.Refinements.FP.NonpreemptiveSched.Job
    (Prosa.Model.Processor.Ideal.processor_state Prosa.Implementation.Refinements.FP.NonpreemptiveSched.Job) :=
fun arr_seq => Prosa.Model.Readiness.Sequential.sequential_ready_instance arr_seq
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_NonpreemptiveSched_sequential_ready_instance
     : Prosa_Behavior_Arrival_sequence_arrival_sequence_inst1
         Prosa_Implementation_Refinements_FP_NonpreemptiveSched_Job
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job ->
       Prosa_Behavior_Ready_JobReady_inst7 Prosa_Implementation_Refinements_FP_NonpreemptiveSched_Job
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
         (Prosa_Model_Processor_Ideal_processor_state_inst1
            Prosa_Implementation_Refinements_FP_NonpreemptiveSched_Job
            Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job)
         Prosa_Implementation_Definitions_Task_JobCost Prosa_Implementation_Definitions_Task_JobArrival
```

Body:

```coq
Prosa_Implementation_Refinements_FP_NonpreemptiveSched_sequential_ready_instance@{} =
fun
  arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence_inst1
              Prosa_Implementation_Refinements_FP_NonpreemptiveSched_Job
              Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job =>
Prosa_Model_Readiness_Sequential_sequential_ready_instance_inst15
  Prosa_Implementation_Refinements_FP_NonpreemptiveSched_Job
  Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
  Prosa_Implementation_Refinements_FP_NonpreemptiveSched_Task
  Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
  Prosa_Implementation_Definitions_Task_JobTask Prosa_Implementation_Definitions_Task_JobArrival
  Prosa_Implementation_Definitions_Task_JobCost
  (Prosa_Model_Processor_Ideal_processor_state_inst1
     Prosa_Implementation_Refinements_FP_NonpreemptiveSched_Job
     Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job)
  arr_seq
     : Prosa_Behavior_Arrival_sequence_arrival_sequence_inst1
         Prosa_Implementation_Refinements_FP_NonpreemptiveSched_Job
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job ->
       Prosa_Behavior_Ready_JobReady_inst7 Prosa_Implementation_Refinements_FP_NonpreemptiveSched_Job
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
         (Prosa_Model_Processor_Ideal_processor_state_inst1
            Prosa_Implementation_Refinements_FP_NonpreemptiveSched_Job
            Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job)
         Prosa_Implementation_Definitions_Task_JobCost Prosa_Implementation_Definitions_Task_JobArrival

Arguments Prosa_Implementation_Refinements_FP_NonpreemptiveSched_sequential_ready_instance arr_seq
```
