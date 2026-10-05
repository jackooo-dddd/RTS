# `not_interference_implies_scheduled`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.restricted_supply.iw_readiness.not_interference_implies_scheduled`
- Lean: `Prosa.Analysis.Abstract.RestrictedSupply.IwReadiness.not_interference_implies_scheduled`
- Certificate: `not_interference_implies_scheduled_correspondence`

## Official Rocq

```coq
not_interference_implies_scheduled :
forall {Job : JobType} {H1 : JobArrival Job} {H2 : JobCost Job} {PState : ProcessorState Job},
@fully_consuming_proc_model Job PState ->
forall {JobReady0 : @JobReady Job PState H2 H1} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall sched : @schedule Job PState,
@valid_schedule Job H1 PState sched H2 JobReady0 arr_seq ->
forall {JLFP : JLFP_policy Job},
@work_conserving Job H1 H2 PState JobReady0 arr_seq sched ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (0 < @job_cost Job H2 j) ->
forall t1 t2 : instant,
@busy_interval_prefix Job H1 H2 PState sched
  (@rs_readiness_jlfp_interference Job H1 H2 PState JobReady0 arr_seq sched JLFP)
  (@rs_readiness_jlfp_interfering_workload Job H1 H2 PState JobReady0 arr_seq sched JLFP) j t1 t2 ->
forall t : instant,
is_true
  (~~ @interference Job (@rs_readiness_jlfp_interference Job H1 H2 PState JobReady0 arr_seq sched JLFP) j t) ->
is_true (@receives_service_at Job PState sched j t)

not_interference_implies_scheduled is not universe polymorphic
Arguments not_interference_implies_scheduled {Job H1 H2 PState} H_consumed_supply_proc_model 
  {JobReady0} arr_seq H_valid_arrival_sequence sched H_valid_schedule {JLFP} H_work_conserving 
  j H_arrives H_job_cost_positive t1 t2 H_busy_interval_prefix t _
not_interference_implies_scheduled is opaque
Expands to: Constant
            prosa.analysis.abstract.restricted_supply.iw_readiness.not_interference_implies_scheduled
Declared in library prosa.analysis.abstract.restricted_supply.iw_readiness, line 511, characters 12-46
@not_interference_implies_scheduled
     : forall (Job : JobType) (H1 : JobArrival Job) (H2 : JobCost Job) (PState : ProcessorState Job),
       @fully_consuming_proc_model Job PState ->
       forall (JobReady0 : @JobReady Job PState H2 H1) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall sched : @schedule Job PState,
       @valid_schedule Job H1 PState sched H2 JobReady0 arr_seq ->
       forall JLFP : JLFP_policy Job,
       @work_conserving Job H1 H2 PState JobReady0 arr_seq sched ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (0 < @job_cost Job H2 j) ->
       forall t1 t2 : instant,
       @busy_interval_prefix Job H1 H2 PState sched
         (@rs_readiness_jlfp_interference Job H1 H2 PState JobReady0 arr_seq sched JLFP)
         (@rs_readiness_jlfp_interfering_workload Job H1 H2 PState JobReady0 arr_seq sched JLFP) j t1 t2 ->
       forall t : instant,
       is_true
         (~~
          @interference Job (@rs_readiness_jlfp_interference Job H1 H2 PState JobReady0 arr_seq sched JLFP) j
            t) ->
       is_true (@receives_service_at Job PState sched j t)
```

## Lean

```lean
@Prosa.Analysis.Abstract.RestrictedSupply.IwReadiness.not_interference_implies_scheduled : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  [inst_2 : Prosa.Behavior.Job.JobCost Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job},
  Prosa.Model.Processor.PlatformProperties.fully_consuming_proc_model PState →
    ∀ [JobReady0 : Prosa.Behavior.Ready.JobReady Job PState]
      (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
      Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
        ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
          Prosa.Behavior.Ready.valid_schedule sched arr_seq →
            ∀ [JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job],
              Prosa.Model.Schedule.WorkConserving.work_conserving arr_seq sched →
                ∀ (j : Job),
                  Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                    0 < Prosa.Behavior.Job.job_cost j →
                      ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                        Prosa.Analysis.Abstract.Definitions.busy_interval_prefix sched j t1 t2 →
                          ∀ (t : Prosa.Behavior.Time.instant),
                            (!Prosa.Analysis.Abstract.Definitions.interference j t) = true →
                              Prosa.Behavior.Service.receives_service_at sched j t = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_RestrictedSupply_IwReadiness_not_interference_implies_scheduled
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : 
          DecidableEq Job)
         (inst_10 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_13 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7),
       Prosa_Model_Processor_PlatformProperties_fully_consuming_proc_model Job
         inst_7 PState ->
       forall
         (JobReady0 : Prosa_Behavior_Ready_JobReady Job
                        inst_7
                        PState
                        inst_13
                        inst_10)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7
         inst_10 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_7
                   PState,
       Prosa_Behavior_Ready_valid_schedule Job
         inst_7
         inst_10 PState
         sched inst_13
         JobReady0 arr_seq ->
       forall
         JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                  inst_7,
       Prosa_Model_Schedule_WorkConserving_work_conserving Job
         inst_7
         inst_10
         inst_13 PState
         JobReady0 arr_seq sched ->
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_7 arr_seq j ->
       LT_lt_inst1 Prosa_Behavior_Job_work instLTNat
         (OfNat_ofNat_inst1 Prosa_Behavior_Job_work 0 (instOfNatNat 0))
         (Prosa_Behavior_Job_JobCost_job_cost Job
            inst_7
            inst_13 j) ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Abstract_Definitions_busy_interval_prefix Job
         inst_7
         (Prosa_Analysis_Abstract_RestrictedSupply_IwReadiness_rs_readiness_jlfp_interference Job
            inst_7
            inst_10
            inst_13 PState
            JobReady0 arr_seq sched JLFP)
         (Prosa_Analysis_Abstract_RestrictedSupply_IwReadiness_rs_readiness_jlfp_interfering_workload Job
            inst_7
            inst_10
            inst_13 PState
            JobReady0 arr_seq sched JLFP)
         inst_10
         inst_13 PState
         sched j t1 t2 ->
       forall t : Prosa_Behavior_Time_instant,
       @eq Bool
         (Bool_not
            (Prosa_Analysis_Abstract_Definitions_Interference_interference Job
               inst_7
               (Prosa_Analysis_Abstract_RestrictedSupply_IwReadiness_rs_readiness_jlfp_interference Job
                  inst_7
                  inst_10
                  inst_13
                  PState JobReady0 arr_seq sched JLFP)
               j t))
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Service_receives_service_at Job
            inst_7 PState
            sched j t)
         Bool_true
```
