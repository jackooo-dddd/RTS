# `t1_relevant`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.edf_opt.t1_relevant`
- Lean: `Prosa.Analysis.Facts.Transform.EdfOpt.t1_relevant`
- Certificate: `t1_relevant_correspondence`

## Official Rocq

```coq
t1_relevant :
forall {Job : JobType} {H1 : JobArrival Job} (sched : @schedule Job (ideal.processor_state Job)),
@jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
forall (j1 : Equality.sort Job) (t1 : instant),
is_true (@scheduled_at Job (ideal.processor_state Job) sched j1 t1) ->
is_true (@relevant_pstate Job H1 t1 (sched t1))

t1_relevant is not universe polymorphic
Arguments t1_relevant {Job H1} sched H_jobs_must_arrive_to_execute j1 t1 H_not_idle
t1_relevant is opaque
Expands to: Constant prosa.analysis.facts.transform.edf_opt.t1_relevant
Declared in library prosa.analysis.facts.transform.edf_opt, line 50, characters 8-19
@t1_relevant
     : forall (Job : JobType) (H1 : JobArrival Job) (sched : @schedule Job (ideal.processor_state Job)),
       @jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
       forall (j1 : Equality.sort Job) (t1 : instant),
       is_true (@scheduled_at Job (ideal.processor_state Job) sched j1 t1) ->
       is_true (@relevant_pstate Job H1 t1 (sched t1))
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.EdfOpt.t1_relevant : ∀ {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job]
  [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
  Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
    ∀ (j1 : Job) (t1 : Prosa.Behavior.Time.instant),
      Prosa.Behavior.Service.scheduled_at sched j1 t1 = true →
        Prosa.Analysis.Transform.EdfTrans.relevant_pstate t1 (sched t1) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_EdfOpt_t1_relevant
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_3)),
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute_inst4 Job
         inst_3
         inst_6
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
       @eq Bool
         (Prosa_Analysis_Transform_EdfTrans_relevant_pstate Job
            inst_3
            inst_6 t1 
            (sched t1))
         Bool_true
```
