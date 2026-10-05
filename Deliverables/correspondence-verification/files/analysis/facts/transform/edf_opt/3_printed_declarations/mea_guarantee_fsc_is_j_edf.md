# `mea_guarantee_fsc_is_j_edf`

- Kind (Rocq): Fact
- Rocq: `prosa.analysis.facts.transform.edf_opt.mea_guarantee_fsc_is_j_edf`
- Lean: `Prosa.Analysis.Facts.Transform.EdfOpt.mea_guarantee_fsc_is_j_edf`
- Certificate: `mea_guarantee_fsc_is_j_edf_correspondence`

## Official Rocq

```coq
mea_guarantee_fsc_is_j_edf :
forall {Job : JobType} {H0 : JobDeadline Job} {H1 : JobArrival Job}
  (sched : @schedule Job (ideal.processor_state Job)) (t_edf : instant) (j_orig : Equality.sort Job),
is_true (@scheduled_at Job (ideal.processor_state Job) sched j_orig t_edf) ->
forall j_edf : Equality.sort Job,
is_true (@scheduled_at Job (ideal.processor_state Job) (@make_edf_at Job H0 H1 sched t_edf) j_edf t_edf) ->
sched (@find_swap_candidate Job H0 H1 sched t_edf j_orig) = @Some (Equality.sort Job) j_edf

mea_guarantee_fsc_is_j_edf is not universe polymorphic
Arguments mea_guarantee_fsc_is_j_edf {Job H0 H1} sched t_edf j_orig H_sched_orig j_edf H_sched_edf
mea_guarantee_fsc_is_j_edf is opaque
Expands to: Constant prosa.analysis.facts.transform.edf_opt.mea_guarantee_fsc_is_j_edf
Declared in library prosa.analysis.facts.transform.edf_opt, line 308, characters 9-35
@mea_guarantee_fsc_is_j_edf
     : forall (Job : JobType) (H0 : JobDeadline Job) (H1 : JobArrival Job)
         (sched : @schedule Job (ideal.processor_state Job)) (t_edf : instant) (j_orig : Equality.sort Job),
       is_true (@scheduled_at Job (ideal.processor_state Job) sched j_orig t_edf) ->
       forall j_edf : Equality.sort Job,
       is_true
         (@scheduled_at Job (ideal.processor_state Job) (@make_edf_at Job H0 H1 sched t_edf) j_edf t_edf) ->
       sched (@find_swap_candidate Job H0 H1 sched t_edf j_orig) = @Some (Equality.sort Job) j_edf
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.EdfOpt.mea_guarantee_fsc_is_j_edf : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobDeadline Job] [inst_2 : Prosa.Behavior.Job.JobArrival Job]
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (t_edf : Prosa.Behavior.Time.instant) (j_orig : Job),
  Prosa.Behavior.Service.scheduled_at sched j_orig t_edf = true →
    ∀ (j_edf : Job),
      Prosa.Behavior.Service.scheduled_at (Prosa.Analysis.Transform.EdfTrans.make_edf_at sched t_edf) j_edf t_edf =
          true →
        sched (Prosa.Analysis.Transform.EdfTrans.find_swap_candidate sched t_edf j_orig) = some j_edf
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_EdfOpt_mea_guarantee_fsc_is_j_edf
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
         (t_edf : Prosa_Behavior_Time_instant) (j_orig : Job),
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            sched j_orig t_edf)
         Bool_true ->
       forall j_edf : Job,
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at_inst4 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            (Prosa_Analysis_Transform_EdfTrans_make_edf_at Job
               inst_3
               inst_6
               inst_9 sched t_edf)
            j_edf t_edf)
         Bool_true ->
       @eq
         (Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3))
         (sched
            (Prosa_Analysis_Transform_EdfTrans_find_swap_candidate Job
               inst_3
               inst_6
               inst_9 sched t_edf j_orig))
         (Option_some Job j_edf)
```
