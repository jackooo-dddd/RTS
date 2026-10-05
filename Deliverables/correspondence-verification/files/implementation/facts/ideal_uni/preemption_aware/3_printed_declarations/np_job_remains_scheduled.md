# `np_job_remains_scheduled`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.facts.ideal_uni.preemption_aware.np_job_remains_scheduled`
- Lean: `Prosa.Implementation.Facts.IdealUni.PreemptionAware.np_job_remains_scheduled`
- Certificate: `np_job_remains_scheduled_correspondence`

## Official Rocq

```coq
np_job_remains_scheduled :
forall {Job : JobType} {H : JobCost Job} {H0 : JobArrival Job} (arr_seq : arrival_sequence Job)
  {RM : @JobReady Job (processor_state Job) H H0} {H1 : JobPreemptable Job}
  (choose_job : instant -> seq (Equality.sort Job) -> option (Equality.sort Job)) 
  (t : nat),
is_true
  (@prev_job_nonpreemptive Job H H0 RM H1
     ((fun t0 : nat =>
       match t0 with
       | 0 => @empty_schedule Job (processor_state Job) (@None (Equality.sort Job))
       | t'.+1 =>
           @schedule_up_to Job (processor_state Job) (@allocation_at Job H H0 arr_seq RM H1 choose_job)
             (@None (Equality.sort Job)) t'
       end) t)
     t) ->
@schedule_up_to Job (processor_state Job) (@allocation_at Job H H0 arr_seq RM H1 choose_job)
  (@None (Equality.sort Job)) t t =
@schedule_up_to Job (processor_state Job) (@allocation_at Job H H0 arr_seq RM H1 choose_job)
  (@None (Equality.sort Job)) t t.-1

np_job_remains_scheduled is not universe polymorphic
Arguments np_job_remains_scheduled {Job H H0} arr_seq {RM H1} choose_job%function_scope t%nat_scope _
np_job_remains_scheduled is opaque
Expands to: Constant prosa.implementation.facts.ideal_uni.preemption_aware.np_job_remains_scheduled
Declared in library prosa.implementation.facts.ideal_uni.preemption_aware, line 207, characters 10-34
@np_job_remains_scheduled
     : forall (Job : JobType) (H : JobCost Job) (H0 : JobArrival Job) (arr_seq : arrival_sequence Job)
         (RM : @JobReady Job (processor_state Job) H H0) (H1 : JobPreemptable Job)
         (choose_job : instant -> seq (Equality.sort Job) -> option (Equality.sort Job)) 
         (t : nat),
       is_true
         (@prev_job_nonpreemptive Job H H0 RM H1
            match t with
            | 0 => @empty_schedule Job (processor_state Job) (@None (Equality.sort Job))
            | t'.+1 =>
                @schedule_up_to Job (processor_state Job) (@allocation_at Job H H0 arr_seq RM H1 choose_job)
                  (@None (Equality.sort Job)) t'
            end t) ->
       @schedule_up_to Job (processor_state Job) (@allocation_at Job H H0 arr_seq RM H1 choose_job)
         (@None (Equality.sort Job)) t t =
       @schedule_up_to Job (processor_state Job) (@allocation_at Job H H0 arr_seq RM H1 choose_job)
         (@None (Equality.sort Job)) t t.-1
```

## Lean

```lean
@Prosa.Implementation.Facts.IdealUni.PreemptionAware.np_job_remains_scheduled : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job] [inst_2 : Prosa.Behavior.Job.JobArrival Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  [RM : Prosa.Behavior.Ready.JobReady Job (Prosa.Model.Processor.Ideal.processor_state Job)]
  [inst_3 : Prosa.Model.Preemption.Parameter.JobPreemptable Job]
  (choose_job : Prosa.Behavior.Time.instant → List Job → Option Job) (t : ℕ),
  Prosa.Implementation.Definitions.IdealUniScheduler.prev_job_nonpreemptive
        (match t with
        | 0 => Prosa.Implementation.Definitions.GenericScheduler.empty_schedule none
        | t'.succ =>
          Prosa.Implementation.Definitions.GenericScheduler.schedule_up_to
            (Prosa.Implementation.Definitions.IdealUniScheduler.allocation_at arr_seq choose_job) none t')
        t =
      true →
    Prosa.Implementation.Definitions.GenericScheduler.schedule_up_to
        (Prosa.Implementation.Definitions.IdealUniScheduler.allocation_at arr_seq choose_job) none t t =
      Prosa.Implementation.Definitions.GenericScheduler.schedule_up_to
        (Prosa.Implementation.Definitions.IdealUniScheduler.allocation_at arr_seq choose_job) none t (t - 1)
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Facts_IdealUni_PreemptionAware_np_job_remains_scheduled
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
                 inst_9)
         (inst_20 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3)
         (choose_job : Prosa_Behavior_Time_instant -> List Job -> Option Job) (t : Nat),
       @eq Bool
         (Prosa_Implementation_Definitions_IdealUniScheduler_prev_job_nonpreemptive Job
            inst_3
            inst_6
            inst_9 RM
            inst_20
            (Prosa_Implementation_Facts_IdealUni_PreemptionAware_np_job_remains_scheduled_match_1
               (fun _ : Nat =>
                Prosa_Behavior_Schedule_schedule_inst4 Job
                  inst_3
                  (Prosa_Model_Processor_Ideal_processor_state Job
                     inst_3))
               t
               (fun _ : Unit =>
                Prosa_Implementation_Definitions_GenericScheduler_empty_schedule_inst2 Job
                  inst_3
                  (Prosa_Model_Processor_Ideal_processor_state Job
                     inst_3)
                  (Option_none Job))
               (fun t' : Nat =>
                Prosa_Implementation_Definitions_GenericScheduler_schedule_up_to_inst2 Job
                  inst_3
                  (Prosa_Model_Processor_Ideal_processor_state Job
                     inst_3)
                  (Prosa_Implementation_Definitions_IdealUniScheduler_allocation_at Job
                     inst_3
                     inst_6
                     inst_9
                     arr_seq RM
                     inst_20
                     choose_job)
                  (Option_none Job) t'))
            t)
         Bool_true ->
       @eq
         (Prosa_Behavior_Schedule_ProcessorState_State_inst2 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3))
         (Prosa_Implementation_Definitions_GenericScheduler_schedule_up_to_inst2 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            (Prosa_Implementation_Definitions_IdealUniScheduler_allocation_at Job
               inst_3
               inst_6
               inst_9
               arr_seq RM
               inst_20
               choose_job)
            (Option_none Job) t t)
         (Prosa_Implementation_Definitions_GenericScheduler_schedule_up_to_inst2 Job
            inst_3
            (Prosa_Model_Processor_Ideal_processor_state Job
               inst_3)
            (Prosa_Implementation_Definitions_IdealUniScheduler_allocation_at Job
               inst_3
               inst_6
               inst_9
               arr_seq RM
               inst_20
               choose_job)
            (Option_none Job) t
            (HSub_hSub_inst7 Nat Prosa_Behavior_Time_instant Nat (instHSub_inst1 Nat instSubNat) t
               (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))))
```
