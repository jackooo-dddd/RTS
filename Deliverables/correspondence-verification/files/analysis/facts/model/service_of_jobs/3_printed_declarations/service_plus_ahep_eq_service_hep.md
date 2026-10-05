# `service_plus_ahep_eq_service_hep`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.service_of_jobs.service_plus_ahep_eq_service_hep`
- Lean: `Prosa.Analysis.Facts.Model.ServiceOfJobs.service_plus_ahep_eq_service_hep`
- Certificate: `service_plus_ahep_eq_service_hep_correspondence`

## Official Rocq

```coq
service_plus_ahep_eq_service_hep :
forall {Job : JobType} {H : JobArrival Job} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H arr_seq ->
forall sched : @schedule Job PState,
@jobs_must_arrive_to_execute Job H PState sched ->
forall {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
forall (t1 t2 : instant) (j : Equality.sort Job),
@arrives_in Job arr_seq j ->
is_true (t1 <= @job_arrival Job H j) ->
@service_during Job PState sched j t1 t2 + @service_of_other_hep_jobs Job PState arr_seq sched JLFP j t1 t2 =
@service_of_hep_jobs Job PState arr_seq sched JLFP j t1 t2

service_plus_ahep_eq_service_hep is not universe polymorphic
Arguments service_plus_ahep_eq_service_hep {Job H PState} arr_seq H_valid_arrival_sequence 
  sched H_jobs_must_arrive_to_execute {JLFP} H_priority_is_reflexive t1 t2 j H_arrives 
  H_t1_le_j_arr
service_plus_ahep_eq_service_hep is opaque
Expands to: Constant prosa.analysis.facts.model.service_of_jobs.service_plus_ahep_eq_service_hep
Declared in library prosa.analysis.facts.model.service_of_jobs, line 265, characters 8-40
@service_plus_ahep_eq_service_hep
     : forall (Job : JobType) (H : JobArrival Job) (PState : ProcessorState Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_must_arrive_to_execute Job H PState sched ->
       forall JLFP : JLFP_policy Job,
       @reflexive_job_priorities Job JLFP ->
       forall (t1 t2 : instant) (j : Equality.sort Job),
       @arrives_in Job arr_seq j ->
       is_true (t1 <= @job_arrival Job H j) ->
       @service_during Job PState sched j t1 t2 +
       @service_of_other_hep_jobs Job PState arr_seq sched JLFP j t1 t2 =
       @service_of_hep_jobs Job PState arr_seq sched JLFP j t1 t2
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.ServiceOfJobs.service_plus_ahep_eq_service_hep : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
      Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
        ∀ (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job),
          Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
            ∀ (t1 t2 : Prosa.Behavior.Time.instant) (j : Job),
              Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                t1 ≤ Prosa.Behavior.Job.job_arrival j →
                  Prosa.Behavior.Service.service_during sched j t1 t2 +
                      Prosa.Model.Aggregate.ServiceOfJobs.service_of_other_hep_jobs arr_seq sched j t1 t2 =
                    Prosa.Model.Aggregate.ServiceOfJobs.service_of_hep_jobs arr_seq sched j t1 t2
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_ServiceOfJobs_service_plus_ahep_eq_service_hep
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_6 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_3 PState,
       Prosa_Behavior_Ready_jobs_must_arrive_to_execute Job
         inst_3
         inst_6 PState sched ->
       forall
         JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                  inst_3,
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_3 JLFP ->
       forall (t1 t2 : Prosa_Behavior_Time_instant) (j : Job),
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat t1
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_3
            inst_6 j) ->
       @eq Prosa_Behavior_Job_work
         (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Nat Prosa_Behavior_Job_work
            (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
            (Prosa_Behavior_Service_service_during Job
               inst_3 PState sched j
               t1 t2)
            (Prosa_Model_Aggregate_ServiceOfJobs_service_of_other_hep_jobs Job
               inst_3 PState arr_seq
               sched JLFP j t1 t2))
         (Prosa_Model_Aggregate_ServiceOfJobs_service_of_hep_jobs Job
            inst_3 PState arr_seq
            sched JLFP j t1 t2)
```
