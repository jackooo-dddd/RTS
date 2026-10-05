# `no_hep_ready_implies_no_service_inversion`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.readiness_interference.no_hep_ready_implies_no_service_inversion`
- Lean: `Prosa.Analysis.Facts.ReadinessInterference.no_hep_ready_implies_no_service_inversion`
- Certificate: `no_hep_ready_implies_no_service_inversion_correspondence`

## Official Rocq

```coq
no_hep_ready_implies_no_service_inversion :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {PState : ProcessorState Job}
  {JobReady0 : @JobReady Job PState H0 H} (arr_seq : arrival_sequence Job) (sched : @schedule Job PState)
  {JLFP : JLFP_policy Job} (j : Equality.sort Job) (t : instant),
is_true (~~ @some_hep_job_ready Job H H0 PState JobReady0 arr_seq sched JLFP j t) ->
is_true (~~ @service_inversion Job H H0 PState JobReady0 arr_seq sched JLFP j t)

no_hep_ready_implies_no_service_inversion is not universe polymorphic
Arguments no_hep_ready_implies_no_service_inversion {Job H H0 PState JobReady0} arr_seq sched {JLFP} j t _
no_hep_ready_implies_no_service_inversion is opaque
Expands to: Constant prosa.analysis.facts.readiness_interference.no_hep_ready_implies_no_service_inversion
Declared in library prosa.analysis.facts.readiness_interference, line 52, characters 8-49
@no_hep_ready_implies_no_service_inversion
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (PState : ProcessorState Job)
         (JobReady0 : @JobReady Job PState H0 H) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job PState) (JLFP : JLFP_policy Job) (j : Equality.sort Job) 
         (t : instant),
       is_true (~~ @some_hep_job_ready Job H H0 PState JobReady0 arr_seq sched JLFP j t) ->
       is_true (~~ @service_inversion Job H H0 PState JobReady0 arr_seq sched JLFP j t)
```

## Lean

```lean
@Prosa.Analysis.Facts.ReadinessInterference.no_hep_ready_implies_no_service_inversion : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  [inst_2 : Prosa.Behavior.Job.JobCost Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  [inst_3 : Prosa.Behavior.Ready.JobReady Job PState] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule PState) [inst_4 : Prosa.Model.Priority.Definitions.JLFP_policy Job]
  (j : Job) (t : Prosa.Behavior.Time.instant),
  (!Prosa.Analysis.Definitions.ReadinessInterference.some_hep_job_ready arr_seq sched j t) = true →
    (!Prosa.Analysis.Definitions.ServiceInversion.ReadinessAware.service_inversion arr_seq sched j t) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_ReadinessInterference_no_hep_ready_implies_no_service_inversion
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (inst_14 : 
          Prosa_Behavior_Ready_JobReady Job
            inst_3 PState
            inst_9
            inst_6)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3 PState)
         (inst_22 : 
          Prosa_Model_Priority_Definitions_JLFP_policy Job
            inst_3)
         (j : Job) (t : Prosa_Behavior_Time_instant),
       @eq Bool
         (Bool_not
            (Prosa_Analysis_Definitions_ReadinessInterference_some_hep_job_ready Job
               inst_3
               inst_6
               inst_9 PState
               inst_14 arr_seq sched
               inst_22 j t))
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Analysis_Definitions_ServiceInversion_ReadinessAware_service_inversion Job
               inst_3
               inst_6
               inst_9 PState
               inst_14 arr_seq sched
               inst_22 j t))
         Bool_true
```
