# `idle_schedule_no_backlogged_jobs`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.ideal_uni.preemption_aware.idle_schedule_no_backlogged_jobs`
- Lean: `Prosa.Implementation.Facts.IdealUni.PreemptionAware.idle_schedule_no_backlogged_jobs`
- Certificate: `idle_schedule_no_backlogged_jobs_correspondence`

## Official Rocq

```coq
idle_schedule_no_backlogged_jobs :
forall {Job : JobType} {H : JobCost Job} {H0 : JobArrival Job} (arr_seq : arrival_sequence Job)
  {RM : @JobReady Job (processor_state Job) H H0},
@nonclairvoyant_readiness Job H H0 (processor_state Job) RM ->
forall {H1 : JobPreemptable Job}
  (choose_job : instant -> seq (Equality.sort Job) -> option (Equality.sort Job)),
(forall (t : instant) (s : seq (Equality.sort Job)), choose_job t s = @None (Equality.sort Job) <-> s = [::]) ->
forall t : instant,
is_true (@ideal_is_idle Job (@pmc_uni_schedule Job H H0 arr_seq RM H1 choose_job) t) ->
@jobs_backlogged_at Job H0 H (processor_state Job) RM arr_seq
  (@pmc_uni_schedule Job H H0 arr_seq RM H1 choose_job) t =

idle_schedule_no_backlogged_jobs is not universe polymorphic
Arguments idle_schedule_no_backlogged_jobs {Job H H0} arr_seq {RM} H_nonclairvoyant_job_readiness 
  {H1} (choose_job H_non_idling)%function_scope t _
idle_schedule_no_backlogged_jobs is opaque
Expands to: Constant prosa.implementation.facts.ideal_uni.preemption_aware.idle_schedule_no_backlogged_jobs
Declared in library prosa.implementation.facts.ideal_uni.preemption_aware, line 72, characters 10-42
@idle_schedule_no_backlogged_jobs
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobArrival Job) (arr_seq : arrival_sequence Job)
         (RM : @JobReady Job (processor_state Job) H H0),
       @nonclairvoyant_readiness Job H H0 (processor_state Job) RM ->
       forall (H1 : JobPreemptable Job)
         (choose_job : instant -> seq (Equality.sort Job) -> option (Equality.sort Job)),
       (forall (t : instant) (s : seq (Equality.sort Job)),
        choose_job t s = @None (Equality.sort Job) <-> s = [::]) ->
       forall t : instant,
       is_true (@ideal_is_idle Job (@pmc_uni_schedule Job H H0 arr_seq RM H1 choose_job) t) ->
       @jobs_backlogged_at Job H0 H (processor_state Job) RM arr_seq
         (@pmc_uni_schedule Job H H0 arr_seq RM H1 choose_job) t =
       [::]
```

## Lean

```lean
@Prosa.Implementation.Facts.IdealUni.PreemptionAware.idle_schedule_no_backlogged_jobs : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  [inst_2 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  [RM : Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Ideal.processor_state Job)],
  Prosa.Analysis.Definitions.Readiness.nonclairvoyant_readiness RM →
    ∀ [inst_3 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
      (choose_job : Prosa.Behavior.Time.instant → List Job → Option Job),
      (∀ (t : Prosa.Behavior.Time.instant) (s : List Job), choose_job t s = none ↔ s = []) →
        ∀ (t : Prosa.Behavior.Time.instant),
          Prosa.Model.Processor.Ideal.ideal_is_idle
                (Prosa.Implementation.Definitions.IdealUniScheduler.pmc_uni_schedule arr_seq choose_job) t =
              true →
            Prosa.Model.Schedule.WorkConserving.jobs_backlogged_at arr_seq
                (Prosa.Implementation.Definitions.IdealUniScheduler.pmc_uni_schedule arr_seq choose_job) t =
              []
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_IdealUni_PreemptionAware_idle_schedule_no_backlogged_jobs
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (RM : Prosa_Behavior_Ready_JobReady_inst4 Job
                 inst_3
                 (Prosa_Model_Processor_Ideal_processor_state Job
                    inst_3)
                 inst_6
                 inst_9),
       Prosa_Analysis_Definitions_Readiness_nonclairvoyant_readiness_inst4 Job
         inst_3
         inst_6
         inst_9
         (Prosa_Model_Processor_Ideal_processor_state Job
            inst_3)
         RM ->
       forall
         (inst_25 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3)
         (choose_job : Prosa_Behavior_Time_instant -> List Job -> Option Job),
       (forall (t : Prosa_Behavior_Time_instant) (s : List Job),
        Iff (@eq (Option Job) (choose_job t s) (Option_none Job)) (@eq (List Job) s (List_nil Job))) ->
       forall t : Prosa_Behavior_Time_instant,
       @eq Bool
         (Prosa_Model_Processor_Ideal_ideal_is_idle Job
            inst_3
            (Prosa_Implementation_Definitions_IdealUniScheduler_pmc_uni_schedule Job
               inst_3
               inst_6
               inst_9
               arr_seq RM
               inst_25
               choose_job)
            t)
         Bool_true ->
       @eq (List Job)
         (Prosa_Model_Schedule_WorkConserving_jobs_backlogged_at_inst4 Job
            inst_3
            inst_9
            inst_6
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            RM arr_seq
            (Prosa_Implementation_Definitions_IdealUniScheduler_pmc_uni_schedule Job
               inst_3
               inst_6
               inst_9
               arr_seq RM
               inst_25
               choose_job)
            t)
         (List_nil Job)
```
