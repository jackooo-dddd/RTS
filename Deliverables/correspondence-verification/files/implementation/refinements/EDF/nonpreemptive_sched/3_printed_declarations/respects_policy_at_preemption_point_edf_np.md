# `respects_policy_at_preemption_point_edf_np`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.refinements.EDF.nonpreemptive_sched.respects_policy_at_preemption_point_edf_np`
- Lean: `Prosa.Implementation.Refinements.EDF.NonpreemptiveSched.respects_policy_at_preemption_point_edf_np`
- Certificate: `respects_policy_at_preemption_point_edf_np_correspondence`

## Official Rocq

```coq
respects_policy_at_preemption_point_edf_np :
forall arr_seq : arrival_sequence Job,
@valid_arrival_sequence Job task.JobArrival arr_seq ->
@respects_JLFP_policy_at_preemption_point Job task.JobArrival task.JobCost (processor_state Job)
  (@fully_nonpreemptive_job_model Job task.JobCost) basic_ready_instance arr_seq 
  (sched arr_seq)
  (@EDF Job
     (@absolute_deadline.job_deadline_from_task_deadline Job
        (@reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality concrete_task)
        task.TaskDeadline task.JobArrival task.JobTask))

respects_policy_at_preemption_point_edf_np is not universe polymorphic
Arguments respects_policy_at_preemption_point_edf_np arr_seq H_valid_arrivals j j_hp t _ _ _ _
respects_policy_at_preemption_point_edf_np is opaque
Expands to: Constant
            prosa.implementation.refinements.EDF.nonpreemptive_sched.respects_policy_at_preemption_point_edf_np
Declared in library prosa.implementation.refinements.EDF.nonpreemptive_sched, line 117, characters 8-50
respects_policy_at_preemption_point_edf_np
     : forall arr_seq : arrival_sequence Job,
       @valid_arrival_sequence Job task.JobArrival arr_seq ->
       @respects_JLFP_policy_at_preemption_point Job task.JobArrival task.JobCost 
         (processor_state Job) (@fully_nonpreemptive_job_model Job task.JobCost) basic_ready_instance arr_seq
         (sched arr_seq)
         (@EDF Job
            (@absolute_deadline.job_deadline_from_task_deadline Job
               (@reverse_coercion eqType Type task_concrete_task__canonical__eqtype_Equality concrete_task)
               task.TaskDeadline task.JobArrival task.JobTask))
```

## Lean

```lean
Prosa.Implementation.Refinements.EDF.NonpreemptiveSched.respects_policy_at_preemption_point_edf_np : ∀
  (arr_seq :
    Prosa.Behavior.Arrival_sequence.arrival_sequence Prosa.Implementation.Refinements.EDF.NonpreemptiveSched.Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq
      (Prosa.Implementation.Refinements.EDF.NonpreemptiveSched.sched arr_seq)
      (Prosa.Model.Priority.Edf.EDF Prosa.Implementation.Refinements.EDF.NonpreemptiveSched.Job)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_respects_policy_at_preemption_point_edf_np
     : forall
         arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence_inst1
                     Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_Job
                     Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job,
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence_inst1
         Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_Job
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
         Prosa_Implementation_Definitions_Task_JobArrival arr_seq ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point_inst7
         Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_Job
         Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
         Prosa_Implementation_Definitions_Task_JobArrival Prosa_Implementation_Definitions_Task_JobCost
         (Prosa_Model_Processor_Ideal_processor_state_inst1
            Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_Job
            Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job)
         (Prosa_Model_Preemption_FullyNonpreemptive_fully_nonpreemptive_job_model_inst1
            Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_Job
            Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
            Prosa_Implementation_Definitions_Task_JobCost)
         Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_basic_ready_instance arr_seq
         (Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_sched arr_seq)
         (Prosa_Model_Priority_Edf_EDF_inst1 Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_Job
            Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
            (Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline_inst3
               Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_Job
               Prosa_Implementation_Refinements_EDF_NonpreemptiveSched_Task
               Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_job
               Prosa_Implementation_Definitions_Task_instDecidableEqConcrete_task
               Prosa_Implementation_Definitions_Task_TaskDeadline
               Prosa_Implementation_Definitions_Task_JobArrival Prosa_Implementation_Definitions_Task_JobTask))
```
