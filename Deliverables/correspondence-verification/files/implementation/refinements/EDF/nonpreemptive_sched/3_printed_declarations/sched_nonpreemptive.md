# `sched_nonpreemptive`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.refinements.EDF.nonpreemptive_sched.sched_nonpreemptive`
- Lean: `Prosa.Implementation.Refinements.EDF.NonpreemptiveSched.sched_nonpreemptive`
- Certificate: `sched_nonpreemptive_correspondence`

## Official Rocq

```coq
sched_nonpreemptive :
forall arr_seq : arrival_sequence Job,
@nonpreemptive_schedule Job task.JobCost (processor_state Job)
  (@uni_schedule Job task.JobCost task.JobArrival arr_seq basic_ready_instance
     (@fully_nonpreemptive_job_model Job task.JobCost)
     (@JLFP_to_JLDP Job
        (@EDF Job
           (@absolute_deadline.job_deadline_from_task_deadline Job
              (@reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality concrete_task)
              task.TaskDeadline task.JobArrival task.JobTask))))

sched_nonpreemptive is not universe polymorphic
Arguments sched_nonpreemptive arr_seq j t t' _ _ _
sched_nonpreemptive is opaque
Expands to: Constant prosa.implementation.refinements.EDF.nonpreemptive_sched.sched_nonpreemptive
Declared in library prosa.implementation.refinements.EDF.nonpreemptive_sched, line 101, characters 8-27
sched_nonpreemptive
     : forall arr_seq : arrival_sequence Job,
       @nonpreemptive_schedule Job task.JobCost (processor_state Job)
         (@uni_schedule Job task.JobCost task.JobArrival arr_seq basic_ready_instance
            (@fully_nonpreemptive_job_model Job task.JobCost)
            (@JLFP_to_JLDP Job
               (@EDF Job
                  (@absolute_deadline.job_deadline_from_task_deadline Job
                     (@reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality
                        concrete_task)
                     task.TaskDeadline task.JobArrival task.JobTask))))
```

## Lean

```lean
Prosa.Implementation.Refinements.EDF.NonpreemptiveSched.sched_nonpreemptive : ∀
  (arr_seq :
    Prosa.Behavior.Arrival_sequence.arrival_sequence Prosa.Implementation.Refinements.EDF.NonpreemptiveSched.Job),
  Prosa.Model.Schedule.Nonpreemptive.nonpreemptive_schedule
    (Prosa.Implementation.Definitions.IdealUniScheduler.uni_schedule arr_seq)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_sched_nonpreemptive
     : forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence_inst1
                     Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_Job
                     Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job,
       Prosa_Model_Schedule_Nonpreemptive_nonpreemptive_schedule_inst7
         Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_Job
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
         Prosa_Implementation_Definitions_Task_JobCost
         (Prosa_Model_Processor_Ideal_processor_state_inst1
            Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_Job
            Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job)
         (Prosa_Implementation_Definitions_IdealUniScheduler_uni_schedule_inst1
            Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_Job
            Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
            Prosa_Implementation_Definitions_Task_JobCost Prosa_Implementation_Definitions_Task_JobArrival
            arr_seq Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_basic_ready_instance
            (Prosa_Model_Preemption_FullyNonpreemptive_fully_nonpreemptive_job_model_inst1
               Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_Job
               Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
               Prosa_Implementation_Definitions_Task_JobCost)
            (Prosa_Model_Priority_Coercion_JLFP_to_JLDP_inst1
               Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_Job
               Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
               (Prosa_Model_Priority_Edf_EDF_inst1
                  Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_Job
                  Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
                  (Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline_inst3
                     Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_Job
                     Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_Task
                     Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
                     Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
                     Prosa_Implementation_Definitions_Task_TaskDeadline
                     Prosa_Implementation_Definitions_Task_JobArrival
                     Prosa_Implementation_Definitions_Task_JobTask))))
```
