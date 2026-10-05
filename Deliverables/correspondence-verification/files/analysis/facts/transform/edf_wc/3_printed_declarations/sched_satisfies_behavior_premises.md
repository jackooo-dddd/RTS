# `sched_satisfies_behavior_premises`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.edf_wc.sched_satisfies_behavior_premises`
- Lean: `Prosa.Analysis.Facts.Transform.EdfWc.sched_satisfies_behavior_premises`
- Certificate: `sched_satisfies_behavior_premises_correspondence`

## Official Rocq

```coq
sched_satisfies_behavior_premises :
forall {Job : JobType} {H : JobCost Job} {H0 : JobDeadline Job} {H1 : JobArrival Job}
  (arr_seq : arrival_sequence Job) (sched : @schedule Job (processor_state Job)),
@valid_schedule Job H1 (processor_state Job) sched H (@basic_ready_instance Job (processor_state Job) H1 H)
  arr_seq ->
@all_deadlines_met Job H H0 (processor_state Job) sched ->
@scheduled_behavior_premises Job H H0 H1 arr_seq sched

sched_satisfies_behavior_premises is not universe polymorphic
Arguments sched_satisfies_behavior_premises {Job H H0 H1} arr_seq sched H_sched_valid H_no_deadline_misses
sched_satisfies_behavior_premises is opaque
Expands to: Constant prosa.analysis.facts.transform.edf_wc.sched_satisfies_behavior_premises
Declared in library prosa.analysis.facts.transform.edf_wc, line 378, characters 8-41
@sched_satisfies_behavior_premises
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobDeadline Job) (H1 : JobArrival Job)
         (arr_seq : arrival_sequence Job) (sched : @schedule Job (processor_state Job)),
       @valid_schedule Job H1 (processor_state Job) sched H
         (@basic_ready_instance Job (processor_state Job) H1 H) arr_seq ->
       @all_deadlines_met Job H H0 (processor_state Job) sched ->
       @scheduled_behavior_premises Job H H0 H1 arr_seq sched
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.EdfWc.sched_satisfies_behavior_premises : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobDeadline Job]
  [inst_3 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
  Prosa.Behavior.Ready.valid_schedule sched arr_seq →
    Prosa.Analysis.Definitions.Schedulability.all_deadlines_met sched →
      Prosa.Analysis.Facts.Transform.EdfWc.scheduled_behavior_premises arr_seq sched
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_EdfWc_sched_satisfies_behavior_premises
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
       Prosa_Analysis_Definitions_Schedulability_all_deadlines_met_inst4 Job
         inst_3
         inst_6
         inst_9
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         sched ->
       Prosa_Analysis_Facts_Transform_EdfWc_scheduled_behavior_premises Job
         inst_3
         inst_6
         inst_9
         inst_12 arr_seq sched
```
