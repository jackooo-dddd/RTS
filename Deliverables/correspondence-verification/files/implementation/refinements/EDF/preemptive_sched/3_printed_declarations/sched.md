# `sched`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.EDF.preemptive_sched.sched`
- Lean: `Prosa.Implementation.Refinements.EDF.PreemptiveSched.sched`
- Certificate: `sched_correspondence`

## Official Rocq

```coq
sched : arrival_sequence Job -> @schedule Job (processor_state Job)

sched is not universe polymorphic
Arguments sched arr_seq _
sched is transparent
Expands to: Constant prosa.implementation.refinements.EDF.preemptive_sched.sched
Declared in library prosa.implementation.refinements.EDF.preemptive_sched, line 34, characters 13-18
sched
     : arrival_sequence Job -> @schedule Job (processor_state Job)
```

Body:

```coq
sched =
fun arr_seq : arrival_sequence Job =>
@uni_schedule Job task.JobCost task.JobArrival arr_seq basic_ready_instance (@fully_preemptive_job_model Job)
  (@JLFP_to_JLDP Job
     (@EDF Job
        (@absolute_deadline.job_deadline_from_task_deadline Job
           (@reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality concrete_task)
           task.TaskDeadline task.JobArrival task.JobTask)))
     : arrival_sequence Job -> @schedule Job (processor_state Job)

Arguments sched arr_seq _
```

## Lean

```lean
Prosa.Implementation.Refinements.EDF.PreemptiveSched.sched : Prosa.Behavior.Arrival_sequence.arrival_sequence
    Prosa.Implementation.Refinements.EDF.PreemptiveSched.Job →
  Prosa.Behavior.Schedule.schedule
    (Prosa.Model.Processor.Ideal.processor_state Prosa.Implementation.Refinements.EDF.PreemptiveSched.Job)
```

Body:

```lean
def Prosa.Implementation.Refinements.EDF.PreemptiveSched.sched : Prosa.Behavior.Arrival_sequence.arrival_sequence
    Prosa.Implementation.Refinements.EDF.PreemptiveSched.Job →
  Prosa.Behavior.Schedule.schedule
    (Prosa.Model.Processor.Ideal.processor_state Prosa.Implementation.Refinements.EDF.PreemptiveSched.Job) :=
fun arr_seq => Prosa.Implementation.Definitions.IdealUniScheduler.uni_schedule arr_seq
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_EDF_PreemptiveSched_sched
     : Prosa_Behavior_Arrival_sequence_arrival_sequence_inst1
         Prosa_Implementation_Refinements_EDF_PreemptiveSched_Job
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job ->
       Prosa_Behavior_Schedule_schedule_inst7 Prosa_Implementation_Refinements_EDF_PreemptiveSched_Job
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
         (Prosa_Model_Processor_Ideal_processor_state_inst1
            Prosa_Implementation_Refinements_EDF_PreemptiveSched_Job
            Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job)
```

Body:

```coq
Prosa_Implementation_Refinements_EDF_PreemptiveSched_sched@{} =
fun
  arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence_inst1
              Prosa_Implementation_Refinements_EDF_PreemptiveSched_Job
              Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job =>
Prosa_Implementation_Definitions_IdealUniScheduler_uni_schedule_inst1
  Prosa_Implementation_Refinements_EDF_PreemptiveSched_Job
  Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
  Prosa_Implementation_Definitions_Task_JobCost Prosa_Implementation_Definitions_Task_JobArrival arr_seq
  Prosa_Implementation_Refinements_EDF_PreemptiveSched_basic_ready_instance
  (Prosa_Model_Preemption_FullyPreemptive_fully_preemptive_job_model_inst1
     Prosa_Implementation_Refinements_EDF_PreemptiveSched_Job
     Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job)
  (Prosa_Model_Priority_Coercion_JLFP_to_JLDP_inst1 Prosa_Implementation_Refinements_EDF_PreemptiveSched_Job
     Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
     (Prosa_Model_Priority_Edf_EDF_inst1 Prosa_Implementation_Refinements_EDF_PreemptiveSched_Job
        Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
        (Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline_inst3
           Prosa_Implementation_Refinements_EDF_PreemptiveSched_Job
           Prosa_Implementation_Refinements_EDF_PreemptiveSched_Task
           Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
           Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
           Prosa_Implementation_Definitions_Task_TaskDeadline
           Prosa_Implementation_Definitions_Task_JobArrival Prosa_Implementation_Definitions_Task_JobTask)))
     : Prosa_Behavior_Arrival_sequence_arrival_sequence_inst1
         Prosa_Implementation_Refinements_EDF_PreemptiveSched_Job
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job ->
       Prosa_Behavior_Schedule_schedule_inst7 Prosa_Implementation_Refinements_EDF_PreemptiveSched_Job
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
         (Prosa_Model_Processor_Ideal_processor_state_inst1
            Prosa_Implementation_Refinements_EDF_PreemptiveSched_Job
            Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job)

Arguments Prosa_Implementation_Refinements_EDF_PreemptiveSched_sched arr_seq a____at____internal__hyg0
```
