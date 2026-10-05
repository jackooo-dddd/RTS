# `fsc_not_idle`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.edf_opt.fsc_not_idle`
- Lean: `Prosa.Analysis.Facts.Transform.EdfOpt.fsc_not_idle`
- Certificate: `fsc_not_idle_correspondence`

## Official Rocq

```coq
fsc_not_idle :
forall {Job : JobType} {H0 : JobDeadline Job} {H1 : JobArrival Job}
  (sched : @schedule Job (ideal.processor_state Job)),
@jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
forall (j1 : Equality.sort Job) (t1 : instant),
is_true (@scheduled_at Job (ideal.processor_state Job) sched j1 t1) ->
is_true (t1 < @job_deadline Job H0 j1) ->
exists j' : Equality.sort Job,
  is_true
    (@scheduled_at Job (ideal.processor_state Job) sched j' (@find_swap_candidate Job H0 H1 sched t1 j1)) /\
  is_true (@job_arrival Job H1 j' <= t1)

fsc_not_idle is not universe polymorphic
Arguments fsc_not_idle {Job H0 H1} sched H_jobs_must_arrive_to_execute j1 t1 H_not_idle H_deadline_not_missed
fsc_not_idle is opaque
Expands to: Constant prosa.analysis.facts.transform.edf_opt.fsc_not_idle
Declared in library prosa.analysis.facts.transform.edf_opt, line 82, characters 8-20
@fsc_not_idle
     : forall (Job : JobType) (H0 : JobDeadline Job) (H1 : JobArrival Job)
         (sched : @schedule Job (ideal.processor_state Job)),
       @jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
       forall (j1 : Equality.sort Job) (t1 : instant),
       is_true (@scheduled_at Job (ideal.processor_state Job) sched j1 t1) ->
       is_true (t1 < @job_deadline Job H0 j1) ->
       exists j' : Equality.sort Job,
         is_true
           (@scheduled_at Job (ideal.processor_state Job) sched j'
              (@find_swap_candidate Job H0 H1 sched t1 j1)) /\
         is_true (@job_arrival Job H1 j' <= t1)
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.EdfOpt.fsc_not_idle : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  [inst_1 : Prosa.Behavior.Job.JobDeadline Job] [inst_2 : Prosa.Behavior.Job.JobArrival Job]
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
  Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
    ∀ (j1 : Job) (t1 : Prosa.Behavior.Time.instant),
      Prosa.Behavior.Service.scheduled_at sched j1 t1 = true →
        t1 < Prosa.Behavior.Job.job_deadline j1 →
          ∃ j',
            Prosa.Behavior.Service.scheduled_at sched j'
                  (Prosa.Analysis.Transform.EdfTrans.find_swap_candidate sched t1 j1) =
                true ∧
              Prosa.Behavior.Job.job_arrival j' ≤ t1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_EdfOpt_fsc_not_idle
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
                       inst_3)),
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4 Job
         inst_3
         inst_9
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         sched ->
       forall (j1 : Job) (t1 : Prosa_Behavior_Time_instant),
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            sched j1 t1)
         Bool_true ->
       LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t1
         (Prosa_Behavior_Job_JobDeadline_job_deadline Job
            inst_3
            inst_6 j1) ->
       Exists Job
         (fun j' : Job =>
          And
            (@eq Bool
               (Prosa_Behavior_Service_scheduled_at_inst4 Job
                  inst_3
                  (Prosa_Model_Processor_Ideal_processor_state Job
                     inst_3)
                  sched j'
                  (Prosa_Analysis_Transform_EdfTrans_find_swap_candidate Job
                     inst_3
                     inst_6
                     inst_9 sched t1 j1))
               Bool_true)
            (LE_le_inst1 Prosa_Behavior_Time_instant instLENat
               (Prosa_Behavior_Job_JobArrival_job_arrival Job
                  inst_3
                  inst_9 j')
               t1))
```
