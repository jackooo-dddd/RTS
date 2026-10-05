# `EDF_optimality`

- Kind (Rocq): Theorem
- Rocq: `prosa.results.optimality.edf.EDF_optimality`
- Lean: `Prosa.Results.Optimality.Edf.EDF_optimality`
- Certificate: `EDF_optimality_correspondence`

## Official Rocq

```coq
EDF_optimality :
forall {Job : JobType} {H : JobCost Job} {H0 : JobDeadline Job} {H1 : JobArrival Job}
  (arr_seq : arrival_sequence Job),
(exists any_sched : @schedule Job (processor_state Job),
   @valid_schedule Job H1 (processor_state Job) any_sched H
     (@basic_ready_instance Job (processor_state Job) H1 H) arr_seq /\
   @all_deadlines_of_arrivals_met Job H H0 (processor_state Job) arr_seq any_sched) ->
exists edf_sched : @schedule Job (processor_state Job),
  @valid_schedule Job H1 (processor_state Job) edf_sched H
    (@basic_ready_instance Job (processor_state Job) H1 H) arr_seq /\
  @all_deadlines_of_arrivals_met Job H H0 (processor_state Job) arr_seq edf_sched /\
  @EDF_schedule Job H0 H1 (processor_state Job) edf_sched

EDF_optimality is not universe polymorphic
Arguments EDF_optimality {Job H H0 H1} arr_seq _
EDF_optimality is opaque
Expands to: Constant prosa.results.optimality.edf.EDF_optimality
Declared in library prosa.results.optimality.edf, line 38, characters 10-24
@EDF_optimality
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobDeadline Job) (H1 : JobArrival Job)
         (arr_seq : arrival_sequence Job),
       (exists any_sched : @schedule Job (processor_state Job),
          @valid_schedule Job H1 (processor_state Job) any_sched H
            (@basic_ready_instance Job (processor_state Job) H1 H) arr_seq /\
          @all_deadlines_of_arrivals_met Job H H0 (processor_state Job) arr_seq any_sched) ->
       exists edf_sched : @schedule Job (processor_state Job),
         @valid_schedule Job H1 (processor_state Job) edf_sched H
           (@basic_ready_instance Job (processor_state Job) H1 H) arr_seq /\
         @all_deadlines_of_arrivals_met Job H H0 (processor_state Job) arr_seq edf_sched /\
         @EDF_schedule Job H0 H1 (processor_state Job) edf_sched
```

## Lean

```lean
@Prosa.Results.Optimality.Edf.EDF_optimality : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  [inst_1 : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobDeadline Job]
  [inst_3 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  (∃ any_sched,
      Prosa.Behavior.Ready.valid_schedule any_sched arr_seq ∧
        Prosa.Analysis.Definitions.Schedulability.all_deadlines_of_arrivals_met arr_seq any_sched) →
    ∃ edf_sched,
      Prosa.Behavior.Ready.valid_schedule edf_sched arr_seq ∧
        Prosa.Analysis.Definitions.Schedulability.all_deadlines_of_arrivals_met arr_seq edf_sched ∧
          Prosa.Model.Schedule.Edf.EDF_schedule edf_sched
```

## Lean, imported into Rocq

```coq
Prosa_Results_Optimality_Edf_EDF_optimality
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
            edf_sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                          inst_3
                          (Prosa_Model_Processor_Ideal_processor_state Job
                             inst_3) =>
          And
            (Prosa_Behavior_Ready_valid_schedule_inst4 Job
               inst_3
               inst_12
               (Prosa_Model_Processor_Ideal_processor_state Job
                  inst_3)
               edf_sched inst_6
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
                  arr_seq edf_sched)
               (Prosa_Model_Schedule_Edf_EDF_schedule_inst4 Job
                  inst_3
                  inst_9
                  inst_12
                  (Prosa_Model_Processor_Ideal_processor_state Job
                     inst_3)
                  edf_sched)))
```
