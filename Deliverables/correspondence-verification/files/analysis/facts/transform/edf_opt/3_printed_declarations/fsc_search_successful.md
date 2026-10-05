# `fsc_search_successful`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.edf_opt.fsc_search_successful`
- Lean: `Prosa.Analysis.Facts.Transform.EdfOpt.fsc_search_successful`
- Certificate: `fsc_search_successful_correspondence`

## Official Rocq

```coq
fsc_search_successful :
forall {Job : JobType} {H0 : JobDeadline Job} {H1 : JobArrival Job}
  (sched : @schedule Job (ideal.processor_state Job)),
@jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
forall (j1 : Equality.sort Job) (t1 : instant),
is_true (@scheduled_at Job (ideal.processor_state Job) sched j1 t1) ->
is_true (t1 < @job_deadline Job H0 j1) ->
exists t : nat,
  @search_arg (@State Job (ideal.processor_state Job)) sched (@relevant_pstate Job H1 t1)
    (@earlier_deadline Job H0) t1 (@job_deadline Job H0 j1) =
  @Some nat t

fsc_search_successful is not universe polymorphic
Arguments fsc_search_successful {Job H0 H1} sched H_jobs_must_arrive_to_execute j1 
  t1 H_not_idle H_deadline_not_missed
fsc_search_successful is opaque
Expands to: Constant prosa.analysis.facts.transform.edf_opt.fsc_search_successful
Declared in library prosa.analysis.facts.transform.edf_opt, line 60, characters 8-29
@fsc_search_successful
     : forall (Job : JobType) (H0 : JobDeadline Job) (H1 : JobArrival Job)
         (sched : @schedule Job (ideal.processor_state Job)),
       @jobs_must_arrive_to_execute Job H1 (ideal.processor_state Job) sched ->
       forall (j1 : Equality.sort Job) (t1 : instant),
       is_true (@scheduled_at Job (ideal.processor_state Job) sched j1 t1) ->
       is_true (t1 < @job_deadline Job H0 j1) ->
       exists t : nat,
         @search_arg (@State Job (ideal.processor_state Job)) sched (@relevant_pstate Job H1 t1)
           (@earlier_deadline Job H0) t1 (@job_deadline Job H0 j1) =
         @Some nat t
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.EdfOpt.fsc_search_successful : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobDeadline Job] [inst_2 : Prosa.Behavior.Job.JobArrival Job]
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job)),
  Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
    ∀ (j1 : Job) (t1 : Prosa.Behavior.Time.instant),
      Prosa.Behavior.Service.scheduled_at sched j1 t1 = true →
        t1 < Prosa.Behavior.Job.job_deadline j1 →
          ∃ t,
            Prosa.Util.SearchArg.search_arg sched (Prosa.Analysis.Transform.EdfTrans.relevant_pstate t1)
                Prosa.Analysis.Transform.EdfTrans.earlier_deadline t1 (Prosa.Behavior.Job.job_deadline j1) =
              some t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_EdfOpt_fsc_search_successful
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
       Exists Nat
         (fun t : Nat =>
          Prosa_Util_SearchArg_search_arg
            (Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
               inst_3
               (Prosa_Model_Processor_Ideal_processor_state Job
                  inst_3))
            sched
            (Prosa_Analysis_Transform_EdfTrans_relevant_pstate Job
               inst_3
               inst_9 t1)
            (Prosa_Analysis_Transform_EdfTrans_earlier_deadline Job
               inst_3
               inst_6)
            t1
            (Prosa_Behavior_Job_JobDeadline_job_deadline Job
               inst_3
               inst_6 j1) =
          Option_some_inst1 Nat t)
```
