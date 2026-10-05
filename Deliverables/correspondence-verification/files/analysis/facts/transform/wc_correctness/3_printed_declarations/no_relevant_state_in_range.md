# `no_relevant_state_in_range`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.wc_correctness.no_relevant_state_in_range`
- Lean: `Prosa.Analysis.Facts.Transform.WcCorrectness.no_relevant_state_in_range`
- Certificate: `no_relevant_state_in_range_correspondence`

## Official Rocq

```coq
no_relevant_state_in_range :
forall {Job : JobType} {H : JobArrival Job} {H1 : JobDeadline Job} (arr_seq : arrival_sequence Job)
  (sched : @schedule Job (processor_state Job)) (t : instant),
@search_result Job H H1 arr_seq sched t = @None nat ->
forall t' : nat,
is_true (t <= t' < @max_deadline_for_jobs_arrived_before Job H1 arr_seq t) ->
is_true (~~ @relevant_pstate Job H t (sched t'))

no_relevant_state_in_range is not universe polymorphic
Arguments no_relevant_state_in_range {Job H H1} arr_seq sched t H_search_result_none t'%nat_scope _
no_relevant_state_in_range is opaque
Expands to: Constant prosa.analysis.facts.transform.wc_correctness.no_relevant_state_in_range
Declared in library prosa.analysis.facts.transform.wc_correctness, line 277, characters 14-40
@no_relevant_state_in_range
     : forall (Job : JobType) (H : JobArrival Job) (H1 : JobDeadline Job) (arr_seq : arrival_sequence Job)
         (sched : @schedule Job (processor_state Job)) (t : instant),
       @search_result Job H H1 arr_seq sched t = @None nat ->
       forall t' : nat,
       is_true (t <= t' < @max_deadline_for_jobs_arrived_before Job H1 arr_seq t) ->
       is_true (~~ @relevant_pstate Job H t (sched t'))
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.WcCorrectness.no_relevant_state_in_range : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobDeadline Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job)
  (sched : Prosa.Behavior.Schedule.schedule (Prosa.Model.Processor.Ideal.processor_state Job))
  (t : Prosa.Behavior.Time.instant),
  Prosa.Analysis.Facts.Transform.WcCorrectness.search_result arr_seq sched t = none →
    ∀ (t' : ℕ),
      (decide (t ≤ t') &&
            decide (t' < Prosa.Analysis.Transform.WcTrans.max_deadline_for_jobs_arrived_before arr_seq t)) =
          true →
        (!Prosa.Analysis.Transform.WcTrans.relevant_pstate t (sched t')) = true
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_WcCorrectness_no_relevant_state_in_range
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobDeadline Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3)
         (sched : Prosa_Behavior_Schedule_schedule_inst4 Job
                    inst_3
                    (Prosa_Model_Processor_Ideal_processor_state Job
                       inst_3))
         (t : Prosa_Behavior_Time_instant),
       @eq (Option_inst1 Nat)
         (Prosa_Analysis_Facts_Transform_WcCorrectness_search_result Job
            inst_3
            inst_6
            inst_9 arr_seq sched t)
         (Option_none_inst1 Nat) ->
       forall t' : Nat,
       @eq Bool
         (Bool_and
            (Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_instant instLENat t t') (Nat_decLe t t'))
            (Decidable_decide
               (LT_lt_inst1 Nat instLTNat t'
                  (Prosa_Analysis_Transform_WcTrans_max_deadline_for_jobs_arrived_before Job
                     inst_3
                     inst_9 arr_seq
                     t))
               (Nat_decLt t'
                  (Prosa_Analysis_Transform_WcTrans_max_deadline_for_jobs_arrived_before Job
                     inst_3
                     inst_9 arr_seq
                     t))))
         Bool_true ->
       @eq Bool
         (Bool_not
            (Prosa_Analysis_Transform_WcTrans_relevant_pstate Job
               inst_3
               inst_6 t 
               (sched t')))
         Bool_true
```
