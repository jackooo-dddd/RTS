# `max_dl_is_greatest_dl`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.transform.wc_correctness.max_dl_is_greatest_dl`
- Lean: `Prosa.Analysis.Facts.Transform.WcCorrectness.max_dl_is_greatest_dl`
- Certificate: `max_dl_is_greatest_dl_correspondence`

## Official Rocq

```coq
max_dl_is_greatest_dl :
forall {Job : JobType} {H : JobArrival Job} {H1 : JobDeadline Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H arr_seq ->
forall (j : Equality.sort Job) (t : nat),
@arrives_in Job arr_seq j ->
is_true (@job_arrival Job H j <= t) ->
is_true (@job_deadline Job H1 j <= @max_deadline_for_jobs_arrived_before Job H1 arr_seq t)

max_dl_is_greatest_dl is not universe polymorphic
Arguments max_dl_is_greatest_dl {Job H H1} arr_seq H_arr_seq_valid j t%nat_scope _ _
max_dl_is_greatest_dl is opaque
Expands to: Constant prosa.analysis.facts.transform.wc_correctness.max_dl_is_greatest_dl
Declared in library prosa.analysis.facts.transform.wc_correctness, line 200, characters 10-31
@max_dl_is_greatest_dl
     : forall (Job : JobType) (H : JobArrival Job) (H1 : JobDeadline Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H arr_seq ->
       forall (j : Equality.sort Job) (t : nat),
       @arrives_in Job arr_seq j ->
       is_true (@job_arrival Job H j <= t) ->
       is_true (@job_deadline Job H1 j <= @max_deadline_for_jobs_arrived_before Job H1 arr_seq t)
```

## Lean

```lean
@Prosa.Analysis.Facts.Transform.WcCorrectness.max_dl_is_greatest_dl : ∀ {Job : Prosa.Behavior.Job.JobType}
  [inst : DecidableEq Job] [inst_1 : Prosa.Behavior.Job.JobArrival Job] [inst_2 : Prosa.Behavior.Job.JobDeadline Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (j : Job) (t : ℕ),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        Prosa.Behavior.Job.job_arrival j ≤ t →
          Prosa.Behavior.Job.job_deadline j ≤
            Prosa.Analysis.Transform.WcTrans.max_deadline_for_jobs_arrived_before arr_seq t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Transform_WcCorrectness_max_dl_is_greatest_dl
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : 
          DecidableEq Job)
         (inst_6 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (inst_9 : 
          Prosa_Behavior_Job_JobDeadline Job
            inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_6 arr_seq ->
       forall (j : Job) (t : Nat),
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_3 arr_seq j ->
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat
         (Prosa_Behavior_Job_JobArrival_job_arrival Job
            inst_3
            inst_6 j)
         t ->
       LE_le_inst1 Prosa_Behavior_Time_instant instLENat
         (Prosa_Behavior_Job_JobDeadline_job_deadline Job
            inst_3
            inst_9 j)
         (Prosa_Analysis_Transform_WcTrans_max_deadline_for_jobs_arrived_before Job
            inst_3
            inst_9 arr_seq t)
```
