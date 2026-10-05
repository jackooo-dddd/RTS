# `EDF_schedule_implies_respects_policy_at_preemption_point`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.edf_definitions.EDF_schedule_implies_respects_policy_at_preemption_point`
- Lean: `Prosa.Analysis.Facts.EdfDefinitions.EDF_schedule_implies_respects_policy_at_preemption_point`
- Certificate: `EDF_schedule_implies_respects_policy_at_preemption_point_correspondence`

## Official Rocq

```coq
EDF_schedule_implies_respects_policy_at_preemption_point :
forall {Job : JobType} {H : JobCost Job} {H0 : JobDeadline Job} {H1 : JobArrival Job}
  (arr_seq : arrival_sequence Job) (sched : @schedule Job (ideal.processor_state Job)),
@all_deadlines_of_arrivals_met Job H H0 (ideal.processor_state Job) arr_seq sched ->
@EDF_schedule Job H0 H1 (ideal.processor_state Job) sched ->
@respects_JLFP_policy_at_preemption_point Job H1 H (ideal.processor_state Job)
  (@fully_preemptive.fully_preemptive_job_model Job)
  (@basic.basic_ready_instance Job (ideal.processor_state Job) H1 H) arr_seq sched 
  (@EDF Job H0)

EDF_schedule_implies_respects_policy_at_preemption_point is not universe polymorphic
Arguments EDF_schedule_implies_respects_policy_at_preemption_point {Job H H0 H1} 
  arr_seq sched H_no_deadline_misses _ j j_hp t _ _ _ _
EDF_schedule_implies_respects_policy_at_preemption_point is opaque
Expands to: Constant
            prosa.analysis.facts.edf_definitions.EDF_schedule_implies_respects_policy_at_preemption_point
Declared in library prosa.analysis.facts.edf_definitions, line 67, characters 8-64
@EDF_schedule_implies_respects_policy_at_preemption_point
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobDeadline Job) (H1 : JobArrival Job)
         (arr_seq : arrival_sequence Job) (sched : @schedule Job (ideal.processor_state Job)),
       @all_deadlines_of_arrivals_met Job H H0 (ideal.processor_state Job) arr_seq sched ->
       @EDF_schedule Job H0 H1 (ideal.processor_state Job) sched ->
       @respects_JLFP_policy_at_preemption_point Job H1 H (ideal.processor_state Job)
         (@fully_preemptive.fully_preemptive_job_model Job)
         (@basic.basic_ready_instance Job (ideal.processor_state Job) H1 H) arr_seq sched 
         (@EDF Job H0)
```

## Lean

```lean
@Prosa.Analysis.Facts.EdfDefinitions.EDF_schedule_implies_respects_policy_at_preemption_point : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  [inst_2 : Prosa.Behavior.Job.JobDeadline Job] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
  Prosa.Analysis.Definitions.Schedulability.all_deadlines_of_arrivals_met arr_seq sched →
    Prosa.Model.Schedule.Edf.EDF_schedule sched →
      Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq sched
        (Prosa.Model.Priority.Edf.EDF Job)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_EdfDefinitions_EDF_schedule_implies_respects_policy_at_preemption_point
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
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_3)),
       Prosa_Analysis_Definitions_Schedulability_all_deadlines_of_arrivals_met_inst4 Job
         inst_3
         inst_6
         inst_9
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         arr_seq sched ->
       Prosa_Model_Schedule_Edf_EDF_schedule_inst4 Job
         inst_3
         inst_9
         inst_12
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         sched ->
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
            inst_9)
```
