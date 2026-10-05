# `edf_prefix_guarantee`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.edf_opt.edf_prefix_guarantee`
- Lean: `Prosa.Analysis.Facts.Transform.EdfOpt.edf_prefix_guarantee`
- Certificate: `edf_prefix_guarantee_correspondence`

## Official Rocq

```coq
edf_prefix_guarantee :
forall {Job : JobType} {H : JobCost Job} {H0 : JobDeadline Job} {H1 : JobArrival Job}
  (sched : @schedule Job (ideal.processor_state Job)),
@jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
@completed_jobs_dont_execute Job (ideal.processor_state Job) sched H ->
@all_deadlines_met Job H H0 (ideal.processor_state Job) sched ->
forall (horizon : instant) (t : nat),
is_true (t < horizon) ->
@EDF_at Job H0 H1 (ideal.processor_state Job) (@edf_transform_prefix Job H0 H1 sched horizon) t

edf_prefix_guarantee is not universe polymorphic
Arguments edf_prefix_guarantee {Job H H0 H1} sched H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_no_deadline_misses horizon t%nat_scope _ j _ t' 
  j' _ _ _
edf_prefix_guarantee is opaque
Expands to: Constant prosa.analysis.facts.transform.edf_opt.edf_prefix_guarantee
Declared in library prosa.analysis.facts.transform.edf_opt, line 634, characters 8-28
@edf_prefix_guarantee
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobDeadline Job) (H1 : JobArrival Job)
         (sched : @schedule Job (ideal.processor_state Job)),
       @jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
       @completed_jobs_dont_execute Job (ideal.processor_state Job) sched H ->
       @all_deadlines_met Job H H0 (ideal.processor_state Job) sched ->
       forall (horizon : instant) (t : nat),
       is_true (t < horizon) ->
       @EDF_at Job H0 H1 (ideal.processor_state Job) (@edf_transform_prefix Job H0 H1 sched horizon) t
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.EdfOpt.edf_prefix_guarantee : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobDeadline Job]
  [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
  Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
    Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
      Prosa.Analysis.Definitions.Schedulability.all_deadlines_met sched →
        ∀ (horizon : Prosa.Behavior.Time.instant),
          ∀ t < horizon,
            Prosa.Model.Schedule.Edf.EDF_at (Prosa.Analysis.Transform.EdfTrans.edf_transform_prefix sched horizon) t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_EdfOpt_edf_prefix_guarantee
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
       forall (horizon : Prosa_Behavior_Time_instant) (t : Nat),
       LT_lt_inst1 Nat instLTNat t horizon ->
       Prosa_Model_Schedule_Edf_EDF_at_inst4 Job
         inst_3
         inst_9
         inst_12
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         (Prosa_Analysis_Transform_EdfTrans_edf_transform_prefix Job
            inst_3
            inst_9
            inst_12 sched horizon)
         t
```
