# `sched_valid`

- Kind (Rocq): Remark
- Rocq: `prosa.implementation.refinements.FP.preemptive_sched.sched_valid`
- Lean: `Prosa.Implementation.Refinements.FP.PreemptiveSched.sched_valid`
- Certificate: `sched_valid_correspondence`

## Official Rocq

```coq
sched_valid :
forall arr_seq : arrival_sequence Job,
@valid_schedule Job JobArrival (processor_state Job) (sched arr_seq) JobCost
  (sequential_ready_instance arr_seq) arr_seq

sched_valid is not universe polymorphic
Arguments sched_valid arr_seq
sched_valid is opaque
Expands to: Constant prosa.implementation.refinements.FP.preemptive_sched.sched_valid
Declared in library prosa.implementation.refinements.FP.preemptive_sched, line 36, characters 9-20
sched_valid
     : forall arr_seq : arrival_sequence Job,
       @valid_schedule Job JobArrival (processor_state Job) (sched arr_seq) JobCost
         (sequential_ready_instance arr_seq) arr_seq
```

## Lean

```lean
Prosa.Implementation.Refinements.FP.PreemptiveSched.sched_valid : ∀
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Prosa.Implementation.Refinements.FP.PreemptiveSched.Job),
  Prosa.Behavior.Ready.valid_schedule (Prosa.Implementation.Refinements.FP.PreemptiveSched.sched arr_seq) arr_seq
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_PreemptiveSched_sched_valid
     : forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence_inst1
                     Prosa_Implementation_Refinements_FP_PreemptiveSched_Job
                     Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job,
       Prosa_Behavior_Ready_valid_schedule_inst7 Prosa_Implementation_Refinements_FP_PreemptiveSched_Job
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
         Prosa_Implementation_Definitions_Task_JobArrival
         (Prosa_Model_Processor_Ideal_processor_state_inst1
            Prosa_Implementation_Refinements_FP_PreemptiveSched_Job
            Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job)
         (Prosa_Implementation_Refinements_FP_PreemptiveSched_sched arr_seq)
         Prosa_Implementation_Definitions_Task_JobCost
         (Prosa_Implementation_Refinements_FP_PreemptiveSched_sequential_ready_instance arr_seq) arr_seq
```
