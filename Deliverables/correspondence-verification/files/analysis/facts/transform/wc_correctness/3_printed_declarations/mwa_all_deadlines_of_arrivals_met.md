# `mwa_all_deadlines_of_arrivals_met`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.wc_correctness.mwa_all_deadlines_of_arrivals_met`
- Lean: `Prosa.Analysis.Facts.Transform.WcCorrectness.mwa_all_deadlines_of_arrivals_met`
- Certificate: `mwa_all_deadlines_of_arrivals_met_correspondence`

## Official Rocq

```coq
mwa_all_deadlines_of_arrivals_met :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {H1 : JobDeadline Job}
  (arr_seq : arrival_sequence Job) (sched : @schedule Job (processor_state Job)) 
  (t : instant),
@all_deadlines_of_arrivals_met Job H0 H1 (processor_state Job) arr_seq sched ->
@all_deadlines_of_arrivals_met Job H0 H1 (processor_state Job) arr_seq (@make_wc_at Job H H1 arr_seq sched t)

mwa_all_deadlines_of_arrivals_met is not universe polymorphic
Arguments mwa_all_deadlines_of_arrivals_met {Job H H0 H1} arr_seq sched t _ j _
mwa_all_deadlines_of_arrivals_met is opaque
Expands to: Constant prosa.analysis.facts.transform.wc_correctness.mwa_all_deadlines_of_arrivals_met
Declared in library prosa.analysis.facts.transform.wc_correctness, line 421, characters 10-43
@mwa_all_deadlines_of_arrivals_met
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (H1 : JobDeadline Job)
         (arr_seq : arrival_sequence Job) (sched : @schedule Job (processor_state Job)) 
         (t : instant),
       @all_deadlines_of_arrivals_met Job H0 H1 (processor_state Job) arr_seq sched ->
       @all_deadlines_of_arrivals_met Job H0 H1 (processor_state Job) arr_seq
         (@make_wc_at Job H H1 arr_seq sched t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.WcCorrectness.mwa_all_deadlines_of_arrivals_met : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobCost Job]
  [inst_3 : Prosa.Behavior.Job.JobDeadline Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (t : Prosa.Behavior.Time.instant),
  Prosa.Analysis.Definitions.Schedulability.all_deadlines_of_arrivals_met arr_seq sched →
    Prosa.Analysis.Definitions.Schedulability.all_deadlines_of_arrivals_met arr_seq
      (Prosa.Analysis.Transform.WcTrans.make_wc_at arr_seq sched t)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_WcCorrectness_mwa_all_deadlines_of_arrivals_met
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_12 : 
          Prosa_Behavior_Job_JobDeadline Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_3))
         (t : Prosa_Behavior_Time_instant),
       Prosa_Analysis_Definitions_Schedulability_all_deadlines_of_arrivals_met_inst4 Job
         inst_3
         inst_9
         inst_12
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         arr_seq sched ->
       Prosa_Analysis_Definitions_Schedulability_all_deadlines_of_arrivals_met_inst4 Job
         inst_3
         inst_9
         inst_12
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         arr_seq
         (Prosa_Analysis_Transform_WcTrans_make_wc_at Job
            inst_3
            inst_6
            inst_12 arr_seq sched
            t)
```
