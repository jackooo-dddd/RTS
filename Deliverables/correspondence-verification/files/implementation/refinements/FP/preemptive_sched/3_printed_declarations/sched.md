# `sched`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.FP.preemptive_sched.sched`
- Lean: `Prosa.Implementation.Refinements.FP.PreemptiveSched.sched`
- Certificate: `sched_correspondence`

## Official Rocq

```coq
sched : arrival_sequence Job -> @schedule Job (processor_state Job)

sched is not universe polymorphic
Arguments sched arr_seq _
sched is transparent
Expands to: Constant prosa.implementation.refinements.FP.preemptive_sched.sched
Declared in library prosa.implementation.refinements.FP.preemptive_sched, line 33, characters 13-18
sched
     : arrival_sequence Job -> @schedule Job (processor_state Job)
```

Body:

```coq
sched =
fun arr_seq : arrival_sequence Job =>
@uni_schedule Job JobCost JobArrival arr_seq (sequential_ready_instance arr_seq)
  (@fully_preemptive_job_model Job)
  (@JLFP_to_JLDP Job
     (@FP_to_JLFP Job
        (@reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality concrete_task) JobTask
        (@NumericFPAscending
           (@reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality concrete_task)
           TaskPriority)))
     : arrival_sequence Job -> @schedule Job (processor_state Job)

Arguments sched arr_seq _
```

## Lean

```lean
Prosa.Implementation.Refinements.FP.PreemptiveSched.sched : Prosa.Behavior.Arrival_sequence.arrival_sequence
    Prosa.Implementation.Refinements.FP.PreemptiveSched.Job →
  Prosa.Behavior.Schedule.schedule
    (Prosa.Model.Processor.Ideal.processor_state Prosa.Implementation.Refinements.FP.PreemptiveSched.Job)
```

Body:

```lean
def Prosa.Implementation.Refinements.FP.PreemptiveSched.sched : Prosa.Behavior.Arrival_sequence.arrival_sequence
    Prosa.Implementation.Refinements.FP.PreemptiveSched.Job →
  Prosa.Behavior.Schedule.schedule
    (Prosa.Model.Processor.Ideal.processor_state Prosa.Implementation.Refinements.FP.PreemptiveSched.Job) :=
fun arr_seq => Prosa.Implementation.Definitions.IdealUniScheduler.uni_schedule arr_seq
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_PreemptiveSched_sched
     : Prosa_Behavior_Arrival_sequence_arrival_sequence_inst1
         Prosa_Implementation_Refinements_FP_PreemptiveSched_Job
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job ->
       Prosa_Behavior_Schedule_schedule_inst7 Prosa_Implementation_Refinements_FP_PreemptiveSched_Job
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
         (Prosa_Model_Processor_Ideal_processor_state_inst1
            Prosa_Implementation_Refinements_FP_PreemptiveSched_Job
            Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job)
```

Body:

```coq
Prosa_Implementation_Refinements_FP_PreemptiveSched_sched@{} =
fun
  arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence_inst1
              Prosa_Implementation_Refinements_FP_PreemptiveSched_Job
              Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job =>
Prosa_Implementation_Definitions_IdealUniScheduler_uni_schedule_inst1
  Prosa_Implementation_Refinements_FP_PreemptiveSched_Job
  Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
  Prosa_Implementation_Definitions_Task_JobCost Prosa_Implementation_Definitions_Task_JobArrival arr_seq
  (Prosa_Implementation_Refinements_FP_PreemptiveSched_sequential_ready_instance arr_seq)
  (Prosa_Model_Preemption_FullyPreemptive_fully_preemptive_job_model_inst1
     Prosa_Implementation_Refinements_FP_PreemptiveSched_Job
     Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job)
  (Prosa_Model_Priority_Coercion_JLFP_to_JLDP_inst1 Prosa_Implementation_Refinements_FP_PreemptiveSched_Job
     Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
     (Prosa_Model_Priority_Coercion_FP_to_JLFP_inst3 Prosa_Implementation_Refinements_FP_PreemptiveSched_Job
        Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
        Prosa_Implementation_Refinements_FP_PreemptiveSched_Task
        Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
        Prosa_Implementation_Definitions_Task_JobTask
        (Prosa_Model_Priority_NumericFixedPriority_NumericFPAscending_inst1
           Prosa_Implementation_Refinements_FP_PreemptiveSched_Task
           Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
           Prosa_Implementation_Definitions_Task_TaskPriority)))
     : Prosa_Behavior_Arrival_sequence_arrival_sequence_inst1
         Prosa_Implementation_Refinements_FP_PreemptiveSched_Job
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job ->
       Prosa_Behavior_Schedule_schedule_inst7 Prosa_Implementation_Refinements_FP_PreemptiveSched_Job
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
         (Prosa_Model_Processor_Ideal_processor_state_inst1
            Prosa_Implementation_Refinements_FP_PreemptiveSched_Job
            Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job)

Arguments Prosa_Implementation_Refinements_FP_PreemptiveSched_sched arr_seq a____at____internal__hyg0
```
