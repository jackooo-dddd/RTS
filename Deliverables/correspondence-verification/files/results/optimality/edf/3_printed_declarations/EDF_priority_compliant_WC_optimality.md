# `EDF_priority_compliant_WC_optimality`

- Kind (Rocq): Corollary
- Rocq: `prosa.results.optimality.edf.EDF_priority_compliant_WC_optimality`
- Lean: `Prosa.Results.Optimality.Edf.EDF_priority_compliant_WC_optimality`
- Certificate: `EDF_priority_compliant_WC_optimality_correspondence`

## Official Rocq

```coq
EDF_priority_compliant_WC_optimality :
forall {Job : JobType} {H : JobCost Job} {H0 : JobDeadline Job} {H1 : JobArrival Job}
  (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
(exists any_sched : @schedule Job (processor_state Job),
   @valid_schedule Job H1 (processor_state Job) any_sched H
     (@basic_ready_instance Job (processor_state Job) H1 H) arr_seq /\
   @all_deadlines_of_arrivals_met Job H H0 (processor_state Job) arr_seq any_sched) ->
exists priority_compliant_sched : @schedule Job (processor_state Job),
  @valid_schedule Job H1 (processor_state Job) priority_compliant_sched H
    (@basic_ready_instance Job (processor_state Job) H1 H) arr_seq /\
  @all_deadlines_of_arrivals_met Job H H0 (processor_state Job) arr_seq priority_compliant_sched /\
  @work_conserving Job H1 H (processor_state Job) (@basic_ready_instance Job (processor_state Job) H1 H)
    arr_seq priority_compliant_sched /\
  @respects_JLFP_policy_at_preemption_point Job H1 H (processor_state Job)
    (@fully_preemptive.fully_preemptive_job_model Job) (@basic_ready_instance Job (processor_state Job) H1 H)
    arr_seq priority_compliant_sched (@EDF Job H0)

EDF_priority_compliant_WC_optimality is not universe polymorphic
Arguments EDF_priority_compliant_WC_optimality {Job H H0 H1} arr_seq H_arr_seq_valid _
EDF_priority_compliant_WC_optimality is opaque
Expands to: Constant prosa.results.optimality.edf.EDF_priority_compliant_WC_optimality
Declared in library prosa.results.optimality.edf, line 107, characters 12-48
@EDF_priority_compliant_WC_optimality
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobDeadline Job) (H1 : JobArrival Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       (exists any_sched : @schedule Job (processor_state Job),
          @valid_schedule Job H1 (processor_state Job) any_sched H
            (@basic_ready_instance Job (processor_state Job) H1 H) arr_seq /\
          @all_deadlines_of_arrivals_met Job H H0 (processor_state Job) arr_seq any_sched) ->
       exists priority_compliant_sched : @schedule Job (processor_state Job),
         @valid_schedule Job H1 (processor_state Job) priority_compliant_sched H
           (@basic_ready_instance Job (processor_state Job) H1 H) arr_seq /\
         @all_deadlines_of_arrivals_met Job H H0 (processor_state Job) arr_seq priority_compliant_sched /\
         @work_conserving Job H1 H (processor_state Job)
           (@basic_ready_instance Job (processor_state Job) H1 H) arr_seq priority_compliant_sched /\
         @respects_JLFP_policy_at_preemption_point Job H1 H (processor_state Job)
           (@fully_preemptive.fully_preemptive_job_model Job)
           (@basic_ready_instance Job (processor_state Job) H1 H) arr_seq priority_compliant_sched
           (@EDF Job H0)
```

## Lean

```lean
@Prosa.Results.Optimality.Edf.EDF_priority_compliant_WC_optimality : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobDeadline Job]
  [inst_3 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    (∃ any_sched,
        Prosa.Behavior.Ready.valid_schedule any_sched arr_seq ∧
          Prosa.Analysis.Definitions.Schedulability.all_deadlines_of_arrivals_met arr_seq any_sched) →
      ∃ priority_compliant_sched,
        Prosa.Behavior.Ready.valid_schedule priority_compliant_sched arr_seq ∧
          Prosa.Analysis.Definitions.Schedulability.all_deadlines_of_arrivals_met arr_seq priority_compliant_sched ∧
            Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq priority_compliant_sched ∧
              Prosa.Model.Schedule.PriorityDriven.respects_JLFP_policy_at_preemption_point arr_seq
                priority_compliant_sched (Prosa.Model.Priority.Edf.EDF Job)
```

## Lean, imported into Rocq

```coq
Prosa_Results_Optimality_Edf_EDF_priority_compliant_WC_optimality
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : Prosa_Behavior_Job_JobCost Job
                                                                               inst_3)
         (inst_9 : Prosa_Behavior_Job_JobDeadline
                                                                               Job
                                                                               inst_3)
         (inst_12 : Prosa_Behavior_Job_JobArrival
                                                                                Job
                                                                                inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_12 arr_seq ->
       Exists
         (Prosa_Behavior_Schedule_schedule_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3))
         (fun
            any_sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                          inst_3
                          (Prosa_Model_Processor_Ideal_processor_state Job
                             inst_3) =>
          And
            (Prosa_Behavior_Ready_valid_schedule_inst4 Job
               inst_3
               inst_12
               (Prosa_Model_Processor_Ideal_processor_state Job
                  inst_3)
               any_sched inst_6
               (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
                  inst_3
                  (Prosa_Model_Processor_Ideal_processor_state Job
                     inst_3)
                  inst_12
                  inst_6)
               arr_seq)
            (Prosa_Analysis_Definitions_Schedulability_all_deadlines_of_arrivals_met_inst4 Job
               inst_3
               inst_6
               inst_9
               (Prosa_Model_Processor_Ideal_processor_state Job
                  inst_3)
               arr_seq any_sched)) ->
       Exists
         (Prosa_Behavior_Schedule_schedule_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3))
         (fun
            priority_compliant_sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                                         inst_3
                                         (Prosa_Model_Processor_Ideal_processor_state Job
                                            inst_3) =>
          And
            (Prosa_Behavior_Ready_valid_schedule_inst4 Job
               inst_3
               inst_12
               (Prosa_Model_Processor_Ideal_processor_state Job
                  inst_3)
               priority_compliant_sched inst_6
               (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
                  inst_3
                  (Prosa_Model_Processor_Ideal_processor_state Job
                     inst_3)
                  inst_12
                  inst_6)
               arr_seq)
            (And
               (Prosa_Analysis_Definitions_Schedulability_all_deadlines_of_arrivals_met_inst4 Job
                  inst_3
                  inst_6
                  inst_9
                  (Prosa_Model_Processor_Ideal_processor_state Job
                     inst_3)
                  arr_seq priority_compliant_sched)
               (And
                  (Prosa_Model_Schedule_WorkConserving_work_conserving_inst4 Job
                     inst_3
                     inst_12
                     inst_6
                     (Prosa_Model_Processor_Ideal_processor_state Job
                        inst_3)
                     (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
                        inst_3
                        (Prosa_Model_Processor_Ideal_processor_state Job
                           inst_3)
                        inst_12
                        inst_6)
                     arr_seq priority_compliant_sched)
                  (Prosa_Model_Schedule_PriorityDriven_respects_JLFP_policy_at_preemption_point_inst4 Job
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
                     arr_seq priority_compliant_sched
                     (Prosa_Model_Priority_Edf_EDF Job
                        inst_3
                        inst_9)))))
```
