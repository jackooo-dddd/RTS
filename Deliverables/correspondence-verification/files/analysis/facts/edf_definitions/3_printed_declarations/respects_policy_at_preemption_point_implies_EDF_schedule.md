# `respects_policy_at_preemption_point_implies_EDF_schedule`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.edf_definitions.respects_policy_at_preemption_point_implies_EDF_schedule`
- Lean: `Prosa.Analysis.Facts.EdfDefinitions.respects_policy_at_preemption_point_implies_EDF_schedule`
- Certificate: `respects_policy_at_preemption_point_implies_EDF_schedule_correspondence`

## Official Rocq

```coq
respects_policy_at_preemption_point_implies_EDF_schedule :
forall {Job : JobType} {H : JobCost Job} {H0 : JobDeadline Job} {H1 : JobArrival Job}
  (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall sched : @schedule Job (ideal.processor_state Job),
@jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
@completed_jobs_dont_execute Job (ideal.processor_state Job) sched H ->
@jobs_come_from_arrival_sequence Job (ideal.processor_state Job) sched arr_seq ->
@respects_JLFP_policy_at_preemption_point Job H1 H (ideal.processor_state Job)
  (@fully_preemptive.fully_preemptive_job_model Job)
  (@basic.basic_ready_instance Job (ideal.processor_state Job) H1 H) arr_seq sched 
  (@EDF Job H0) ->
@EDF_schedule Job H0 H1 (ideal.processor_state Job) sched

respects_policy_at_preemption_point_implies_EDF_schedule is not universe polymorphic
Arguments respects_policy_at_preemption_point_implies_EDF_schedule {Job H H0 H1} 
  arr_seq H_arr_seq_valid sched H_jobs_must_arrive_to_execute H_completed_jobs_dont_execute 
  H_from_arr_seq _ t j _ t' j' _ _ _
respects_policy_at_preemption_point_implies_EDF_schedule is opaque
Expands to: Constant
            prosa.analysis.facts.edf_definitions.respects_policy_at_preemption_point_implies_EDF_schedule
Declared in library prosa.analysis.facts.edf_definitions, line 84, characters 8-64
@respects_policy_at_preemption_point_implies_EDF_schedule
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobDeadline Job) (H1 : JobArrival Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall sched : @schedule Job (ideal.processor_state Job),
       @jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
       @completed_jobs_dont_execute Job (ideal.processor_state Job) sched H ->
       @jobs_come_from_arrival_sequence Job (ideal.processor_state Job) sched arr_seq ->
       @respects_JLFP_policy_at_preemption_point Job H1 H (ideal.processor_state Job)
         (@fully_preemptive.fully_preemptive_job_model Job)
         (@basic.basic_ready_instance Job (ideal.processor_state Job) H1 H) arr_seq sched 
         (@EDF Job H0) ->
       @EDF_schedule Job H0 H1 (ideal.processor_state Job) sched
```

## Lean

```lean
@Prosa.Analysis.Facts.EdfDefinitions.respects_policy_at_preemption_point_implies_EDF_schedule : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  [inst_2 : Prosa.Behavior.Job.JobDeadline Job] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
      Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
        Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
          Prosa.Behavior.Ready.jobs_come_from_arrival_sequence sched arr_seq →
            Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched
                (Prosa.Model.Priority.Edf.EDF Job) →
              Prosa.Model.Schedule.Edf.EDF_schedule sched
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_EdfDefinitions_respects_policy_at_preemption_point_implies_EDF_schedule
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobDeadline Job
            inst_3)
         (inst_12 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_12 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                   inst_3
                   (Prosa_Model_Processor_Ideal_processor_state Job
                      inst_3),
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4 Job
         inst_3
         inst_12
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         sched ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         sched inst_6 ->
       Prosa_Behavior_Ready_jobs_come_from_arrival_sequence_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         sched arr_seq ->
       Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point_inst4 Job
         inst_3
         inst_12
         inst_6
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         (Prosa_Model_Preemption_FullyPreemptive_fully_preemptive_job_model Job
            inst_3)
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            inst_12
            inst_6)
         arr_seq sched
         (Prosa_Model_Priority_Edf_EDF Job
            inst_3
            inst_9) ->
       Prosa_Model_Schedule_Edf_EDF_schedule_inst4 Job
         inst_3
         inst_9
         inst_12
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         sched
```
