# `sched_jobs_must_be_ready_to_execute`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.refinements.EDF.nonpreemptive_sched.sched_jobs_must_be_ready_to_execute`
- Lean: `Prosa.Implementation.Refinements.EDF.NonpreemptiveSched.sched_jobs_must_be_ready_to_execute`
- Certificate: `sched_jobs_must_be_ready_to_execute_correspondence`

## Official Rocq

```coq
sched_jobs_must_be_ready_to_execute :
forall arr_seq : arrival_sequence Job,
@jobs_must_be_ready_to_execute Job task.JobArrival (processor_state Job) (sched arr_seq) task.JobCost
  basic_ready_instance

sched_jobs_must_be_ready_to_execute is not universe polymorphic
Arguments sched_jobs_must_be_ready_to_execute arr_seq j t _
sched_jobs_must_be_ready_to_execute is opaque
Expands to: Constant
            prosa.implementation.refinements.EDF.nonpreemptive_sched.sched_jobs_must_be_ready_to_execute
Declared in library prosa.implementation.refinements.EDF.nonpreemptive_sched, line 38, characters 8-43
sched_jobs_must_be_ready_to_execute
     : forall arr_seq : arrival_sequence Job,
       @jobs_must_be_ready_to_execute Job task.JobArrival (processor_state Job) (sched arr_seq) task.JobCost
         basic_ready_instance
```

## Lean

```lean
Prosa.Implementation.Refinements.EDF.NonpreemptiveSched.sched_jobs_must_be_ready_to_execute : ∀
  (arr_seq :
    Prosa.Behavior.Arrival_sequence.arrival_sequence Prosa.Implementation.Refinements.EDF.NonpreemptiveSched.Job),
  Prosa.Behavior.Ready.jobs_must_be_ready_to_execute
    (Prosa.Implementation.Refinements.EDF.NonpreemptiveSched.sched arr_seq)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_sched_jobs_must_be_ready_to_execute
     : forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence_inst1
                     Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_Job
                     Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job,
       Prosa_Behavior_Ready_jobs_must_be_ready_to_execute_inst7
         Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_Job
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
         Prosa_Implementation_Definitions_Task_JobArrival
         (Prosa_Model_Processor_Ideal_processor_state_inst1
            Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_Job
            Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job)
         (Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_sched arr_seq)
         Prosa_Implementation_Definitions_Task_JobCost
         Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_basic_ready_instance
```
