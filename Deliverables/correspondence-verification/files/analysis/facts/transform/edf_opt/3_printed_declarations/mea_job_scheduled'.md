# `mea_job_scheduled'`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.edf_opt.mea_job_scheduled'`
- Lean: `Prosa.Analysis.Facts.Transform.EdfOpt.mea_job_scheduled'`
- Certificate: `mea_job_scheduled'_correspondence`

## Official Rocq

```coq
mea_job_scheduled' :
forall {Job : JobType} {H0 : JobDeadline Job} {H1 : JobArrival Job}
  (sched : @schedule Job (ideal.processor_state Job)) (t_edf : instant) (j : Equality.sort Job) 
  (t : instant),
is_true (@scheduled_at Job (ideal.processor_state Job) sched j t) ->
exists t' : instant,
  is_true (@scheduled_at Job (ideal.processor_state Job) (@make_edf_at Job H0 H1 sched t_edf) j t')

mea_job_scheduled' is not universe polymorphic
Arguments mea_job_scheduled' {Job H0 H1} sched t_edf j t _
mea_job_scheduled' is opaque
Expands to: Constant prosa.analysis.facts.transform.edf_opt.mea_job_scheduled'
Declared in library prosa.analysis.facts.transform.edf_opt, line 442, characters 8-26
@mea_job_scheduled'
     : forall (Job : JobType) (H0 : JobDeadline Job) (H1 : JobArrival Job)
         (sched : @schedule Job (ideal.processor_state Job)) (t_edf : instant) (j : Equality.sort Job)
         (t : instant),
       is_true (@scheduled_at Job (ideal.processor_state Job) sched j t) ->
       exists t' : instant,
         is_true (@scheduled_at Job (ideal.processor_state Job) (@make_edf_at Job H0 H1 sched t_edf) j t')
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.EdfOpt.mea_job_scheduled' : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobDeadline Job] [inst_2 : Prosa.Behavior.Job.JobArrival Job]
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (t_edf : Prosa.Behavior.Time.instant) (j : Job) (t : Prosa.Behavior.Time.instant),
  Prosa.Behavior.Service.scheduled_at sched j t = true →
    ∃ t', Prosa.Behavior.Service.scheduled_at (Prosa.Analysis.Transform.EdfTrans.make_edf_at sched t_edf) j t' = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_EdfOpt_mea_job_scheduled'
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobDeadline Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_3))
         (t_edf : Prosa_Behavior_Time_instant) (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            sched j t)
         Bool_true ->
       Exists Prosa_Behavior_Time_instant
         (fun t' : Prosa_Behavior_Time_instant =>
          Prosa_Behavior_Service_scheduled_at_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            (Prosa_Analysis_Transform_EdfTrans_make_edf_at Job
               inst_3
               inst_6
               inst_9 sched t_edf)
            j t' =
          Bool_true)
```
