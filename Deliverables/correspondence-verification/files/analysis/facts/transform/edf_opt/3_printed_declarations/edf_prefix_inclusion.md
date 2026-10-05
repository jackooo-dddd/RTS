# `edf_prefix_inclusion`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.edf_opt.edf_prefix_inclusion`
- Lean: `Prosa.Analysis.Facts.Transform.EdfOpt.edf_prefix_inclusion`
- Certificate: `edf_prefix_inclusion_correspondence`

## Official Rocq

```coq
edf_prefix_inclusion :
forall {Job : JobType} {H : JobCost Job} {H0 : JobDeadline Job} {H1 : JobArrival Job}
  (sched : @schedule Job (ideal.processor_state Job)),
@jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
@completed_jobs_dont_execute Job (ideal.processor_state Job) sched H ->
@all_deadlines_met Job H H0 (ideal.processor_state Job) sched ->
forall h1 h2 : nat,
is_true (h1 <= h2) ->
@identical_prefix Job (ideal.processor_state Job) (@edf_transform_prefix Job H0 H1 sched h1)
  (@edf_transform_prefix Job H0 H1 sched h2) h1

edf_prefix_inclusion is not universe polymorphic
Arguments edf_prefix_inclusion {Job H H0 H1} sched H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_no_deadline_misses (h1 h2)%nat_scope _ t _
edf_prefix_inclusion is opaque
Expands to: Constant prosa.analysis.facts.transform.edf_opt.edf_prefix_inclusion
Declared in library prosa.analysis.facts.transform.edf_opt, line 678, characters 8-28
@edf_prefix_inclusion
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobDeadline Job) (H1 : JobArrival Job)
         (sched : @schedule Job (ideal.processor_state Job)),
       @jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
       @completed_jobs_dont_execute Job (ideal.processor_state Job) sched H ->
       @all_deadlines_met Job H H0 (ideal.processor_state Job) sched ->
       forall h1 h2 : nat,
       is_true (h1 <= h2) ->
       @identical_prefix Job (ideal.processor_state Job) (@edf_transform_prefix Job H0 H1 sched h1)
         (@edf_transform_prefix Job H0 H1 sched h2) h1
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.EdfOpt.edf_prefix_inclusion : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobDeadline Job]
  [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
  Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
    Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
      Prosa.Analysis.Definitions.Schedulability.all_deadlines_met sched →
        ∀ (h1 h2 : ℕ),
          h1 ≤ h2 →
            Prosa.Analysis.Definitions.SchedulePrefix.identical_prefix
              (Prosa.Analysis.Transform.EdfTrans.edf_transform_prefix sched h1)
              (Prosa.Analysis.Transform.EdfTrans.edf_transform_prefix sched h2) h1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_EdfOpt_edf_prefix_inclusion
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
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_3)),
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
       Prosa_Analysis_Definitions_Schedulability_all_deadlines_met_inst4 Job
         inst_3
         inst_6
         inst_9
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         sched ->
       forall h1 h2 : Nat,
       LE_le_inst1 Nat instLENat h1 h2 ->
       Prosa_Analysis_Definitions_SchedulePrefix_identical_prefix_inst4 Job
         inst_3
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         (Prosa_Analysis_Transform_EdfTrans_edf_transform_prefix Job
            inst_3
            inst_9
            inst_12 sched h1)
         (Prosa_Analysis_Transform_EdfTrans_edf_transform_prefix Job
            inst_3
            inst_9
            inst_12 sched h2)
         h1
```
