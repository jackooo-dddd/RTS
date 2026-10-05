# `edf_schedule_meets_all_deadlines_wrt_arrivals`

- Kind (Rocq): Theorem
- Rocq: `prosa.analysis.facts.transform.edf_opt.edf_schedule_meets_all_deadlines_wrt_arrivals`
- Lean: `Prosa.Analysis.Facts.Transform.EdfOpt.edf_schedule_meets_all_deadlines_wrt_arrivals`
- Certificate: `edf_schedule_meets_all_deadlines_wrt_arrivals_correspondence`

## Official Rocq

```coq
edf_schedule_meets_all_deadlines_wrt_arrivals :
forall {Job : JobType} {H : JobCost Job} {H0 : JobDeadline Job} {H1 : JobArrival Job}
  (arr_seq : arrival_sequence Job) (sched : @schedule Job (ideal.processor_state Job)),
@valid_schedule Job H1 (ideal.processor_state Job) sched H
  (@basic_ready_instance Job (ideal.processor_state Job) H1 H) arr_seq ->
@all_deadlines_of_arrivals_met Job H H0 (ideal.processor_state Job) arr_seq sched ->
@all_deadlines_of_arrivals_met Job H H0 (ideal.processor_state Job) arr_seq (@edf_transform Job H0 H1 sched)

edf_schedule_meets_all_deadlines_wrt_arrivals is not universe polymorphic
Arguments edf_schedule_meets_all_deadlines_wrt_arrivals {Job H H0 H1} arr_seq sched 
  H_sched_valid H_no_deadline_misses_of_arrivals j _
edf_schedule_meets_all_deadlines_wrt_arrivals is opaque
Expands to: Constant prosa.analysis.facts.transform.edf_opt.edf_schedule_meets_all_deadlines_wrt_arrivals
Declared in library prosa.analysis.facts.transform.edf_opt, line 904, characters 12-57
@edf_schedule_meets_all_deadlines_wrt_arrivals
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobDeadline Job) (H1 : JobArrival Job)
         (arr_seq : arrival_sequence Job) (sched : @schedule Job (ideal.processor_state Job)),
       @valid_schedule Job H1 (ideal.processor_state Job) sched H
         (@basic_ready_instance Job (ideal.processor_state Job) H1 H) arr_seq ->
       @all_deadlines_of_arrivals_met Job H H0 (ideal.processor_state Job) arr_seq sched ->
       @all_deadlines_of_arrivals_met Job H H0 (ideal.processor_state Job) arr_seq
         (@edf_transform Job H0 H1 sched)
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.EdfOpt.edf_schedule_meets_all_deadlines_wrt_arrivals : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  [inst_2 : Prosa.Behavior.Job.JobDeadline Job] [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
  Prosa.Behavior.Ready.valid_schedule sched arr_seq →
    Prosa.Analysis.Definitions.Schedulability.all_deadlines_of_arrivals_met arr_seq sched →
      Prosa.Analysis.Definitions.Schedulability.all_deadlines_of_arrivals_met arr_seq
        (Prosa.Analysis.Transform.EdfTrans.edf_transform sched)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_EdfOpt_edf_schedule_meets_all_deadlines_wrt_arrivals
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
       Prosa_Behavior_Ready_valid_schedule_inst4 Job
         inst_3
         inst_12
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         sched inst_6
         (Prosa_Model_Readiness_Basic_basic_ready_instance_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            inst_12
            inst_6)
         arr_seq ->
       Prosa_Analysis_Definitions_Schedulability_all_deadlines_of_arrivals_met_inst4 Job
         inst_3
         inst_6
         inst_9
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         arr_seq sched ->
       Prosa_Analysis_Definitions_Schedulability_all_deadlines_of_arrivals_met_inst4 Job
         inst_3
         inst_6
         inst_9
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         arr_seq
         (Prosa_Analysis_Transform_EdfTrans_edf_transform Job
            inst_3
            inst_9
            inst_12 sched)
```
