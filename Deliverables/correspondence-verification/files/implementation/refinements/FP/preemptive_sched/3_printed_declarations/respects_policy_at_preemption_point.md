# `respects_policy_at_preemption_point`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.refinements.FP.preemptive_sched.respects_policy_at_preemption_point`
- Lean: `Prosa.Implementation.Refinements.FP.PreemptiveSched.respects_policy_at_preemption_point`
- Certificate: `respects_policy_at_preemption_point_correspondence`

## Official Rocq

```coq
respects_policy_at_preemption_point :
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job JobArrival arr_seq ->
@respects_FP_policy_at_preemption_point Task Job JobTask JobArrival JobCost (processor_state Job)
  (@fully_preemptive_job_model Job) (sequential_ready_instance arr_seq) arr_seq (sched arr_seq)
  (@NumericFPAscending Task TaskPriority)

respects_policy_at_preemption_point is not universe polymorphic
Arguments respects_policy_at_preemption_point arr_seq H_valid_arrivals j j_hp t _ _ _ _
respects_policy_at_preemption_point is opaque
Expands to: Constant prosa.implementation.refinements.FP.preemptive_sched.respects_policy_at_preemption_point
Declared in library prosa.implementation.refinements.FP.preemptive_sched, line 44, characters 8-43
respects_policy_at_preemption_point
     : forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job JobArrival arr_seq ->
       @respects_FP_policy_at_preemption_point Task Job JobTask JobArrival JobCost 
         (processor_state Job) (@fully_preemptive_job_model Job) (sequential_ready_instance arr_seq) arr_seq
         (sched arr_seq) (@NumericFPAscending Task TaskPriority)
```

## Lean

```lean
Prosa.Implementation.Refinements.FP.PreemptiveSched.respects_policy_at_preemption_point : ∀
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Prosa.Implementation.Refinements.FP.PreemptiveSched.Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    Prosa.Model.Schedule.PriorityDriven.respects_FP_policy_at_preemption_point arr_seq
      (Prosa.Implementation.Refinements.FP.PreemptiveSched.sched arr_seq)
      (Prosa.Model.Priority.NumericFixedPriority.NumericFPAscending
        Prosa.Implementation.Refinements.FP.PreemptiveSched.Task)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_PreemptiveSched_respects_policy_at_preemption_point
     : forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence_inst1
                     Prosa_Implementation_Refinements_FP_PreemptiveSched_Job
                     Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence_inst1
         Prosa_Implementation_Refinements_FP_PreemptiveSched_Job
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
         Prosa_Implementation_Definitions_Task_JobArrival arr_seq ->
       Prosa_Model_Schedule_PriorityDriven_respects_FP_policy_at_preemption_point_inst15
         Prosa_Implementation_Refinements_FP_PreemptiveSched_Task
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
         Prosa_Implementation_Refinements_FP_PreemptiveSched_Job
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
         Prosa_Implementation_Definitions_Task_JobTask Prosa_Implementation_Definitions_Task_JobArrival
         Prosa_Implementation_Definitions_Task_JobCost
         (Prosa_Model_Processor_Ideal_processor_state_inst1
            Prosa_Implementation_Refinements_FP_PreemptiveSched_Job
            Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job)
         (Prosa_Model_Preemption_FullyPreemptive_fully_preemptive_job_model_inst1
            Prosa_Implementation_Refinements_FP_PreemptiveSched_Job
            Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job)
         (Prosa_Implementation_Refinements_FP_PreemptiveSched_sequential_ready_instance arr_seq) arr_seq
         (Prosa_Implementation_Refinements_FP_PreemptiveSched_sched arr_seq)
         (Prosa_Model_Priority_NumericFixedPriority_NumericFPAscending_inst1
            Prosa_Implementation_Refinements_FP_PreemptiveSched_Task
            Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
            Prosa_Implementation_Definitions_Task_TaskPriority)
```
