# `respects_policy_at_preemption_point_np`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.refinements.FP.nonpreemptive_sched.respects_policy_at_preemption_point_np`
- Lean: `Prosa.Implementation.Refinements.FP.NonpreemptiveSched.respects_policy_at_preemption_point_np`
- Certificate: `respects_policy_at_preemption_point_np_correspondence`

## Official Rocq

```coq
respects_policy_at_preemption_point_np :
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job JobArrival arr_seq ->
@respects_FP_policy_at_preemption_point Task Job JobTask JobArrival JobCost (processor_state Job)
  (@fully_nonpreemptive_job_model Job JobCost) (sequential_ready_instance arr_seq) arr_seq 
  (sched arr_seq) (@NumericFPAscending Task TaskPriority)

respects_policy_at_preemption_point_np is not universe polymorphic
Arguments respects_policy_at_preemption_point_np arr_seq H_valid_arrivals j j_hp t _ _ _ _
respects_policy_at_preemption_point_np is opaque
Expands to: Constant
            prosa.implementation.refinements.FP.nonpreemptive_sched.respects_policy_at_preemption_point_np
Declared in library prosa.implementation.refinements.FP.nonpreemptive_sched, line 118, characters 8-46
respects_policy_at_preemption_point_np
     : forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job JobArrival arr_seq ->
       @respects_FP_policy_at_preemption_point Task Job JobTask JobArrival JobCost 
         (processor_state Job) (@fully_nonpreemptive_job_model Job JobCost)
         (sequential_ready_instance arr_seq) arr_seq (sched arr_seq) (@NumericFPAscending Task TaskPriority)
```

## Lean

```lean
Prosa.Implementation.Refinements.FP.NonpreemptiveSched.respects_policy_at_preemption_point_np : ∀
  (arr_seq :
    Prosa.Behavior.Arrival_sequence.arrival_sequence Prosa.Implementation.Refinements.FP.NonpreemptiveSched.Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    Prosa.Model.Schedule.PriorityDriven.respects_FP_policy_at_preemption_point arr_seq
      (Prosa.Implementation.Refinements.FP.NonpreemptiveSched.sched arr_seq)
      (Prosa.Model.Priority.NumericFixedPriority.NumericFPAscending
        Prosa.Implementation.Refinements.FP.NonpreemptiveSched.Task)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_FP_NonpreemptiveSched_respects_policy_at_preemption_point_np
     : forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence_inst1
                     Prosa_Implementation_Refinements_FP_NonpreemptiveSched_Job
                     Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence_inst1
         Prosa_Implementation_Refinements_FP_NonpreemptiveSched_Job
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
         Prosa_Implementation_Definitions_Task_JobArrival arr_seq ->
       Prosa_Model_Schedule_PriorityDriven_respects_FP_policy_at_preemption_point_inst15
         Prosa_Implementation_Refinements_FP_NonpreemptiveSched_Task
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
         Prosa_Implementation_Refinements_FP_NonpreemptiveSched_Job
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
         Prosa_Implementation_Definitions_Task_JobTask Prosa_Implementation_Definitions_Task_JobArrival
         Prosa_Implementation_Definitions_Task_JobCost
         (Prosa_Model_Processor_Ideal_processor_state_inst1
            Prosa_Implementation_Refinements_FP_NonpreemptiveSched_Job
            Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job)
         (Prosa_Model_Preemption_FullyNonpreemptive_fully_nonpreemptive_job_model_inst1
            Prosa_Implementation_Refinements_FP_NonpreemptiveSched_Job
            Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
            Prosa_Implementation_Definitions_Task_JobCost)
         (Prosa_Implementation_Refinements_FP_NonpreemptiveSched_sequential_ready_instance arr_seq) arr_seq
         (Prosa_Implementation_Refinements_FP_NonpreemptiveSched_sched arr_seq)
         (Prosa_Model_Priority_NumericFixedPriority_NumericFPAscending_inst1
            Prosa_Implementation_Refinements_FP_NonpreemptiveSched_Task
            Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
            Prosa_Implementation_Definitions_Task_TaskPriority)
```
