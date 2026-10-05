# `weak_EDF_optimality`

- Kind (Rocq): Theorem
- Rocq: `prosa.results.optimality.edf.weak_EDF_optimality`
- Lean: `Prosa.Results.Optimality.Edf.weak_EDF_optimality`
- Certificate: `weak_EDF_optimality_correspondence`

## Official Rocq

```coq
weak_EDF_optimality :
forall {Job : JobType} {H : JobCost Job} {H0 : JobDeadline Job} {H1 : JobArrival Job}
  (any_sched : @schedule Job (processor_state Job)),
@jobs_must_arrive_to_execute Job H1 (processor_state Job) any_sched ->
@completed_jobs_dont_execute Job (processor_state Job) any_sched H ->
@all_deadlines_met Job H H0 (processor_state Job) any_sched ->
exists edf_sched : @schedule Job (processor_state Job),
  @jobs_must_arrive_to_execute Job H1 (processor_state Job) edf_sched /\
  @completed_jobs_dont_execute Job (processor_state Job) edf_sched H /\
  @all_deadlines_met Job H H0 (processor_state Job) edf_sched /\
  @EDF_schedule Job H0 H1 (processor_state Job) edf_sched /\
  (forall j : Equality.sort Job,
   (exists t : instant, is_true (@scheduled_at Job (processor_state Job) any_sched j t)) <->
   (exists t' : instant, is_true (@scheduled_at Job (processor_state Job) edf_sched j t')))

weak_EDF_optimality is not universe polymorphic
Arguments weak_EDF_optimality {Job H H0 H1} any_sched H_must_arrive H_completed_dont_execute
  H_all_deadlines_met
weak_EDF_optimality is opaque
Expands to: Constant prosa.results.optimality.edf.weak_EDF_optimality
Declared in library prosa.results.optimality.edf, line 149, characters 10-29
@weak_EDF_optimality
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobDeadline Job) (H1 : JobArrival Job)
         (any_sched : @schedule Job (processor_state Job)),
       @jobs_must_arrive_to_execute Job H1 (processor_state Job) any_sched ->
       @completed_jobs_dont_execute Job (processor_state Job) any_sched H ->
       @all_deadlines_met Job H H0 (processor_state Job) any_sched ->
       exists edf_sched : @schedule Job (processor_state Job),
         @jobs_must_arrive_to_execute Job H1 (processor_state Job) edf_sched /\
         @completed_jobs_dont_execute Job (processor_state Job) edf_sched H /\
         @all_deadlines_met Job H H0 (processor_state Job) edf_sched /\
         @EDF_schedule Job H0 H1 (processor_state Job) edf_sched /\
         (forall j : Equality.sort Job,
          (exists t : instant, is_true (@scheduled_at Job (processor_state Job) any_sched j t)) <->
          (exists t' : instant, is_true (@scheduled_at Job (processor_state Job) edf_sched j t')))
```

## Lean

```lean
@Prosa.Results.Optimality.Edf.weak_EDF_optimality : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  [inst_1 : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobDeadline Job]
  [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  (any_sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
  Prosa.Behavior.Ready.jobs_must_arrive_to_execute any_sched →
    Prosa.Behavior.Ready.completed_jobs_dont_execute any_sched →
      Prosa.Analysis.Definitions.Schedulability.all_deadlines_met any_sched →
        ∃ edf_sched,
          Prosa.Behavior.Ready.jobs_must_arrive_to_execute edf_sched ∧
            Prosa.Behavior.Ready.completed_jobs_dont_execute edf_sched ∧
              Prosa.Analysis.Definitions.Schedulability.all_deadlines_met edf_sched ∧
                Prosa.Model.Schedule.Edf.EDF_schedule edf_sched ∧
                  ∀ (j : Job),
                    (∃ t, Prosa.Behavior.Service.scheduled_at any_sched j t = true) ↔
                      ∃ t', Prosa.Behavior.Service.scheduled_at edf_sched j t' = true
```

## Lean, imported into Rocq

```coq
Prosa_Results_Optimality_Edf_weak_EDF_optimality
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
         (any_sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                        inst_3
                        (Prosa_Model_Processor_Ideal_processor_state Job
                           inst_3)),
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4 Job
         inst_3
         inst_12
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         any_sched ->
       Prosa_Behavior_Ready_completed_jobs_dont_execute_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         any_sched inst_6 ->
       Prosa_Analysis_Definitions_Schedulability_all_deadlines_met_inst4 Job
         inst_3
         inst_6
         inst_9
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         any_sched ->
       Exists
         (Prosa_Behavior_Schedule_schedule_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3))
         (fun
            edf_sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                          inst_3
                          (Prosa_Model_Processor_Ideal_processor_state Job
                             inst_3) =>
          And
            (Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4 Job
               inst_3
               inst_12
               (Prosa_Model_Processor_Ideal_processor_state Job
                  inst_3)
               edf_sched)
            (And
               (Prosa_Behavior_Ready_completed_jobs_dont_execute_inst4 Job
                  inst_3
                  (Prosa_Model_Processor_Ideal_processor_state Job
                     inst_3)
                  edf_sched inst_6)
               (And
                  (Prosa_Analysis_Definitions_Schedulability_all_deadlines_met_inst4 Job
                     inst_3
                     inst_6
                     inst_9
                     (Prosa_Model_Processor_Ideal_processor_state Job
                        inst_3)
                     edf_sched)
                  (And
                     (Prosa_Model_Schedule_Edf_EDF_schedule_inst4 Job
                        inst_3
                        inst_9
                        inst_12
                        (Prosa_Model_Processor_Ideal_processor_state Job
                           inst_3)
                        edf_sched)
                     (forall j : Job,
                      Iff
                        (Exists Prosa_Behavior_Time_instant
                           (fun t : Prosa_Behavior_Time_instant =>
                            Prosa_Behavior_Service_scheduled_at_inst4 Job
                              inst_3
                              (Prosa_Model_Processor_Ideal_processor_state Job
                                 inst_3)
                              any_sched j t =
                            Bool_true))
                        (Exists Prosa_Behavior_Time_instant
                           (fun t' : Prosa_Behavior_Time_instant =>
                            Prosa_Behavior_Service_scheduled_at_inst4 Job
                              inst_3
                              (Prosa_Model_Processor_Ideal_processor_state Job
                                 inst_3)
                              edf_sched j t' =
                            Bool_true)))))))
```
