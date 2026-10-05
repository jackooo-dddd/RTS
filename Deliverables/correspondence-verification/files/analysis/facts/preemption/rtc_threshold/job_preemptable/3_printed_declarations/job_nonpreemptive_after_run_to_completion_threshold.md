# `job_nonpreemptive_after_run_to_completion_threshold`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_nonpreemptive_after_run_to_completion_threshold`
- Lean: `Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable.job_nonpreemptive_after_run_to_completion_threshold`
- Certificate: `job_nonpreemptive_after_run_to_completion_threshold_correspondence`

## Official Rocq

```coq
job_nonpreemptive_after_run_to_completion_threshold :
forall {Job : JobType} {H0 : JobCost Job} {H1 : JobPreemptable Job} {PState : ProcessorState Job}
  (arr_seq : arrival_sequence Job) (sched : @schedule Job PState),
@valid_preemption_model Job H0 H1 PState arr_seq sched ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
forall t t' : nat,
is_true (t <= t') ->
is_true (@job_rtct Job H0 H1 j <= @service Job PState sched j t) ->
is_true (~~ @completed_by Job PState sched H0 j t') -> is_true (@scheduled_at Job PState sched j t')

job_nonpreemptive_after_run_to_completion_threshold is not universe polymorphic
Arguments job_nonpreemptive_after_run_to_completion_threshold {Job H0 H1 PState} 
  arr_seq sched H_valid_preemption_model j H_j_arrives (t t')%nat_scope _ _ _
job_nonpreemptive_after_run_to_completion_threshold is opaque
Expands to: Constant
            prosa.analysis.facts.preemption.rtc_threshold.job_preemptable.job_nonpreemptive_after_run_to_completion_threshold
Declared in library prosa.analysis.facts.preemption.rtc_threshold.job_preemptable, line 241, characters 8-59
@job_nonpreemptive_after_run_to_completion_threshold
     : forall (Job : JobType) (H0 : JobCost Job) (H1 : JobPreemptable Job) (PState : ProcessorState Job)
         (arr_seq : arrival_sequence Job) (sched : @schedule Job PState),
       @valid_preemption_model Job H0 H1 PState arr_seq sched ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       forall t t' : nat,
       is_true (t <= t') ->
       is_true (@job_rtct Job H0 H1 j <= @service Job PState sched j t) ->
       is_true (~~ @completed_by Job PState sched H0 j t') -> is_true (@scheduled_at Job PState sched j t')
```

## Lean

```lean
@Prosa.Analysis.Facts.Preemption.RtcThreshold.JobPreemptable.job_nonpreemptive_after_run_to_completion_threshold : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobCost Job]
  [inst_2 : Prosa.Model.Preemption.Parameter.JobPreemptable Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (sched : Prosa.Behavior.Schedule.schedule PState),
  Prosa.Model.Preemption.Parameter.valid_preemption_model arr_seq sched →
    ∀ (j : Job),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        ∀ (t t' : ℕ),
          t ≤ t' →
            Prosa.Model.Preemption.Parameter.job_rtct j ≤ Prosa.Behavior.Service.service sched j t →
              (!Prosa.Behavior.Service.completed_by sched j t') = true →
                Prosa.Behavior.Service.scheduled_at sched j t' = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Preemption_RtcThreshold_JobPreemptable_job_nonpreemptive_after_run_to_completion_threshold
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_9 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_3
                    PState),
       Prosa_Model_Preemption_Parameter_valid_preemption_model Job
         inst_3
         inst_6
         inst_9
         PState arr_seq sched ->
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3
         arr_seq j ->
       forall t t' : Nat,
       LE_le_inst1 Nat instLENat t t' ->
       LE_le_inst1 Nat instLENat
         (Prosa_Model_Preemption_Parameter_job_rtct Job
            inst_3
            inst_6
            inst_9
            j)
         (Prosa_Behavior_Service_service Job
            inst_3
            PState sched j t) ->
       @eq Bool
         (Bool_not
            (Prosa_Behavior_Service_completed_by Job
               inst_3
               PState sched
               inst_6
               j t'))
         Bool_true ->
       @eq Bool
         (Prosa_Behavior_Service_scheduled_at Job
            inst_3
            PState sched j t')
         Bool_true
```
