# `busy_prefix_starts_when_hep_job_arrives`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.busy_interval.arrival.busy_prefix_starts_when_hep_job_arrives`
- Lean: `Prosa.Analysis.Facts.BusyInterval.Arrival.busy_prefix_starts_when_hep_job_arrives`
- Certificate: `busy_prefix_starts_when_hep_job_arrives_correspondence`

## Official Rocq

```coq
busy_prefix_starts_when_hep_job_arrives :
forall {Job : JobType} {H : JobArrival Job} {H0 : JobCost Job} {JLFP : JLFP_policy Job},
@reflexive_job_priorities Job JLFP ->
forall {PState : ProcessorState Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H arr_seq ->
forall sched : @schedule Job PState,
@jobs_must_arrive_to_execute Job H PState sched ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_cost_positive Job H0 j) ->
forall t1 t2 : instant,
@busy_interval_prefix Job H H0 PState arr_seq sched JLFP j t1 t2 ->
exists j_a : Equality.sort Job, is_true (@arrives_at Job arr_seq j_a t1) /\ is_true (@hep_job Job JLFP j_a j)

busy_prefix_starts_when_hep_job_arrives is not universe polymorphic
Arguments busy_prefix_starts_when_hep_job_arrives {Job H H0 JLFP} H_JLFP_reflexive 
  {PState} arr_seq H_valid_arrival_sequence sched H_jobs_must_arrive_to_execute j 
  H_from_arrival_sequence H_job_cost_positive t1 t2 _
busy_prefix_starts_when_hep_job_arrives is opaque
Expands to: Constant prosa.analysis.facts.busy_interval.arrival.busy_prefix_starts_when_hep_job_arrives
Declared in library prosa.analysis.facts.busy_interval.arrival, line 82, characters 8-47
@busy_prefix_starts_when_hep_job_arrives
     : forall (Job : JobType) (H : JobArrival Job) (H0 : JobCost Job) (JLFP : JLFP_policy Job),
       @reflexive_job_priorities Job JLFP ->
       forall (PState : ProcessorState Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H arr_seq ->
       forall sched : @schedule Job PState,
       @jobs_must_arrive_to_execute Job H PState sched ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (@job_cost_positive Job H0 j) ->
       forall t1 t2 : instant,
       @busy_interval_prefix Job H H0 PState arr_seq sched JLFP j t1 t2 ->
       exists j_a : Equality.sort Job,
         is_true (@arrives_at Job arr_seq j_a t1) /\ is_true (@hep_job Job JLFP j_a j)
```

## Lean

```lean
@Prosa.Analysis.Facts.BusyInterval.Arrival.busy_prefix_starts_when_hep_job_arrives : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job]
  [inst_2 : Prosa.Behavior.Job.JobCost Job] (JLFP : Prosa.Model.Priority.Definitions.JLFP_policy Job),
  Prosa.Model.Priority.Definitions.reflexive_job_priorities JLFP →
    ∀ {PState : Prosa.Behavior.Schedule.ProcessorState Job}
      (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
      Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
        ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
          Prosa.Behavior.Ready.jobs_must_arrive_to_execute sched →
            ∀ (j : Job),
              Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
                Prosa.Model.Job.Properties.job_cost_positive j = true →
                  ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                    Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j t1 t2 →
                      ∃ j_a,
                        Prosa.Behavior.Arrival_sequence.arrives_at arr_seq j_a t1 = true ∧
                          Prosa.Model.Priority.Definitions.hep_job j_a j = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BusyInterval_Arrival_busy_prefix_starts_when_hep_job_arrives
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (JLFP : Prosa_Model_Priority_Definitions_JLFP_policy Job
                   inst_3),
       Prosa_Model_Priority_Definitions_reflexive_job_priorities Job
         inst_3 JLFP ->
       forall
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
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_3
            inst_9 j)
         Bool_true ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix Job
         inst_3
         inst_6
         inst_9 PState arr_seq sched
         JLFP j t1 t2 ->
       Exists Job
         (fun j_a : Job =>
          And
            (@eq Bool
               (Prosa_Behavior_Arrival_sequence_arrives_at Job
                  inst_3 arr_seq j_a
                  t1)
               Bool_true)
            (@eq Bool
               (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
                  inst_3 JLFP j_a j)
               Bool_true))
```
