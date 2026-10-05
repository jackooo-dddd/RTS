# `edf_transform_jobs_must_arrive`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.edf_opt.edf_transform_jobs_must_arrive`
- Lean: `Prosa.Analysis.Facts.Transform.EdfOpt.edf_transform_jobs_must_arrive`
- Certificate: `edf_transform_jobs_must_arrive_correspondence`

## Official Rocq

```coq
edf_transform_jobs_must_arrive :
forall {Job : JobType} {H : JobCost Job} {H0 : JobDeadline Job} {H1 : JobArrival Job}
  (sched : @schedule Job (ideal.processor_state Job)),
@jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
@completed_jobs_dont_execute Job (ideal.processor_state Job) sched H ->
@all_deadlines_met Job H H0 (ideal.processor_state Job) sched ->
@jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) (@edf_transform Job H0 H1 sched)

edf_transform_jobs_must_arrive is not universe polymorphic
Arguments edf_transform_jobs_must_arrive {Job H H0 H1} sched H_jobs_must_arrive_to_execute
  H_completed_jobs_dont_execute H_no_deadline_misses j t _
edf_transform_jobs_must_arrive is opaque
Expands to: Constant prosa.analysis.facts.transform.edf_opt.edf_transform_jobs_must_arrive
Declared in library prosa.analysis.facts.transform.edf_opt, line 766, characters 8-38
@edf_transform_jobs_must_arrive
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobDeadline Job) (H1 : JobArrival Job)
         (sched : @schedule Job (ideal.processor_state Job)),
       @jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
       @completed_jobs_dont_execute Job (ideal.processor_state Job) sched H ->
       @all_deadlines_met Job H H0 (ideal.processor_state Job) sched ->
       @jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) (@edf_transform Job H0 H1 sched)
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.EdfOpt.edf_transform_jobs_must_arrive : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobDeadline Job]
  [inst_3 : Prosa.Behavior.Job.JobArrival Job]
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
  Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
    Prosa.Behavior.Ready.completed_jobs_dont_execute sched →
      Prosa.Analysis.Definitions.Schedulability.all_deadlines_met sched →
        Prosa.Behavior.Ready.jobs_must_arrive_to_execute (Prosa.Analysis.Transform.EdfTrans.edf_transform sched)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_EdfOpt_edf_transform_jobs_must_arrive
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
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4 Job
         inst_3
         inst_12
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         (Prosa_Analysis_Transform_EdfTrans_edf_transform Job
            inst_3
            inst_9
            inst_12 sched)
```
