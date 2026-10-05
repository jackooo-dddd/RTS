# `sched_nonpreemptive`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.refinements.FP.nonpreemptive_sched.sched_nonpreemptive`
- Lean: `Prosa.Implementation.Refinements.FP.NonpreemptiveSched.sched_nonpreemptive`
- Certificate: `sched_nonpreemptive_correspondence`

## Official Rocq

```coq
sched_nonpreemptive :
forall arr_seq : arrival_sequence Job,
@nonpreemptive_schedule Job JobCost (processor_state Job)
  (@uni_schedule Job JobCost JobArrival arr_seq (sequential_ready_instance arr_seq)
     (@fully_nonpreemptive_job_model Job JobCost)
     (@JLFP_to_JLDP Job
        (@FP_to_JLFP Job
           (@reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality concrete_task)
           JobTask
           (@NumericFPAscending
              (@reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality concrete_task)
              TaskPriority))))

sched_nonpreemptive is not universe polymorphic
Arguments sched_nonpreemptive arr_seq j t t' _ _ _
sched_nonpreemptive is opaque
Expands to: Constant prosa.implementation.refinements.FP.nonpreemptive_sched.sched_nonpreemptive
Declared in library prosa.implementation.refinements.FP.nonpreemptive_sched, line 103, characters 8-27
sched_nonpreemptive
     : forall arr_seq : arrival_sequence Job,
       @nonpreemptive_schedule Job JobCost (processor_state Job)
         (@uni_schedule Job JobCost JobArrival arr_seq (sequential_ready_instance arr_seq)
            (@fully_nonpreemptive_job_model Job JobCost)
            (@JLFP_to_JLDP Job
               (@FP_to_JLFP Job
                  (@reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality concrete_task)
                  JobTask
                  (@NumericFPAscending
                     (@reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality
                        concrete_task)
                     TaskPriority))))
```

## Lean

```lean
Prosa.Implementation.Refinements.FP.NonpreemptiveSched.sched_nonpreemptive : ∀
  (arr_seq :
    Prosa.Behavior.Arrival_sequence.arrival_sequence Prosa.Implementation.Refinements.FP.NonpreemptiveSched.Job),
  Prosa.Model.Schedule.Nonpreemptive.nonpreemptive_schedule
    (Prosa.Implementation.Definitions.IdealUniScheduler.uni_schedule arr_seq)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_NonpreemptiveSched_sched_nonpreemptive
     : forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence_inst1
                     Prosa_Implementation_Refinements_FP_NonpreemptiveSched_Job
                     Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job,
       Prosa_Model_Schedule_Nonpreemptive_nonpreemptive_schedule_inst7
         Prosa_Implementation_Refinements_FP_NonpreemptiveSched_Job
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
         Prosa_Implementation_Definitions_Task_JobCost
         (Prosa_Model_Processor_Ideal_processor_state_inst1
            Prosa_Implementation_Refinements_FP_NonpreemptiveSched_Job
            Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job)
         (Prosa_Implementation_Definitions_IdealUniScheduler_uni_schedule_inst1
            Prosa_Implementation_Refinements_FP_NonpreemptiveSched_Job
            Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
            Prosa_Implementation_Definitions_Task_JobCost Prosa_Implementation_Definitions_Task_JobArrival
            arr_seq
            (Prosa_Implementation_Refinements_FP_NonpreemptiveSched_sequential_ready_instance arr_seq)
            (Prosa_Model_Preemption_FullyNonpreemptive_fully_nonpreemptive_job_model_inst1
               Prosa_Implementation_Refinements_FP_NonpreemptiveSched_Job
               Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
               Prosa_Implementation_Definitions_Task_JobCost)
            (Prosa_Model_Priority_Coercion_JLFP_to_JLDP_inst1
               Prosa_Implementation_Refinements_FP_NonpreemptiveSched_Job
               Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
               (Prosa_Model_Priority_Coercion_FP_to_JLFP_inst3
                  Prosa_Implementation_Refinements_FP_NonpreemptiveSched_Job
                  Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
                  Prosa_Implementation_Refinements_FP_NonpreemptiveSched_Task
                  Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
                  Prosa_Implementation_Definitions_Task_JobTask
                  (Prosa_Model_Priority_NumericFixedPriority_NumericFPAscending_inst1
                     Prosa_Implementation_Refinements_FP_NonpreemptiveSched_Task
                     Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
                     Prosa_Implementation_Definitions_Task_TaskPriority))))
```
