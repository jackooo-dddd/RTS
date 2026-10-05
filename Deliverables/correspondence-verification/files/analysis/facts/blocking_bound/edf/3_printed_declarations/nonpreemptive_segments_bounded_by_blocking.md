# `nonpreemptive_segments_bounded_by_blocking`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.blocking_bound.edf.nonpreemptive_segments_bounded_by_blocking`
- Lean: `Prosa.Analysis.Facts.BlockingBound.Edf.nonpreemptive_segments_bounded_by_blocking`
- Certificate: `nonpreemptive_segments_bounded_by_blocking_correspondence`

## Official Rocq

```coq
nonpreemptive_segments_bounded_by_blocking :
forall {Task : TaskType} {H : TaskCost Task} {H0 : MaxArrivals Task} {H1 : TaskDeadline Task}
  {H2 : TaskMaxNonpreemptiveSegment Task} {Job : JobType} {H3 : JobTask Job Task} 
  {H4 : JobCost Job} {H5 : JobArrival Job} {PState : ProcessorState Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H5 arr_seq ->
forall sched : @schedule Job PState,
@arrivals_have_valid_job_costs Task H Job H3 H4 arr_seq ->
forall {H6 : JobPreemptable Job},
@valid_model_with_bounded_nonpreemptive_segments Task Job H3 H4 H2 H6 PState arr_seq sched ->
forall ts : seq (Equality.sort Task),
@all_jobs_from_taskset Task Job H3 arr_seq ts ->
forall tsk : Equality.sort Task,
is_true (tsk \in ts) ->
@taskset_respects_max_arrivals Task Job H3 arr_seq H0 ts ->
forall j : Equality.sort Job,
is_true (@job_of_task Job Task H3 tsk j) ->
forall t1 t2 : instant,
@busy_interval_prefix Job H5 H4 PState arr_seq sched
  (@EDF Job (@job_deadline_from_task_deadline Job Task H1 H5 H3)) j t1 t2 ->
is_true
  (@max_lp_nonpreemptive_segment Job H4 arr_seq
     (@EDF Job (@job_deadline_from_task_deadline Job Task H1 H5 H3)) H6 j t1 <=
   @blocking_bound Task H H1 H2 ts H0 tsk (@job_arrival Job H5 j - t1))

nonpreemptive_segments_bounded_by_blocking is not universe polymorphic
Arguments nonpreemptive_segments_bounded_by_blocking {Task H H0 H1 H2 Job H3 H4 H5 PState} 
  arr_seq H_valid_arrival_sequence sched H_valid_job_cost {H6}
  H_valid_model_with_bounded_nonpreemptive_segments ts%seq_scope H_all_jobs_from_taskset 
  tsk H_tsk_in_ts H_is_arrival_curve j H_job_of_tsk t1 t2 _
nonpreemptive_segments_bounded_by_blocking is opaque
Expands to: Constant prosa.analysis.facts.blocking_bound.edf.nonpreemptive_segments_bounded_by_blocking
Declared in library prosa.analysis.facts.blocking_bound.edf, line 73, characters 8-50
@nonpreemptive_segments_bounded_by_blocking
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (H1 : TaskDeadline Task)
         (H2 : TaskMaxNonpreemptiveSegment Task) (Job : JobType) (H3 : JobTask Job Task) 
         (H4 : JobCost Job) (H5 : JobArrival Job) (PState : ProcessorState Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H5 arr_seq ->
       forall sched : @schedule Job PState,
       @arrivals_have_valid_job_costs Task H Job H3 H4 arr_seq ->
       forall H6 : JobPreemptable Job,
       @valid_model_with_bounded_nonpreemptive_segments Task Job H3 H4 H2 H6 PState arr_seq sched ->
       forall ts : seq (Equality.sort Task),
       @all_jobs_from_taskset Task Job H3 arr_seq ts ->
       forall tsk : Equality.sort Task,
       is_true (tsk \in ts) ->
       @taskset_respects_max_arrivals Task Job H3 arr_seq H0 ts ->
       forall j : Equality.sort Job,
       is_true (@job_of_task Job Task H3 tsk j) ->
       forall t1 t2 : instant,
       @busy_interval_prefix Job H5 H4 PState arr_seq sched
         (@EDF Job (@job_deadline_from_task_deadline Job Task H1 H5 H3)) j t1 t2 ->
       is_true
         (@max_lp_nonpreemptive_segment Job H4 arr_seq
            (@EDF Job (@job_deadline_from_task_deadline Job Task H1 H5 H3)) H6 j t1 <=
          @blocking_bound Task H H1 H2 ts H0 tsk (@job_arrival Job H5 j - t1))
```

## Lean

```lean
@Prosa.Analysis.Facts.BlockingBound.Edf.nonpreemptive_segments_bounded_by_blocking : ∀
  {Job : Prosa.Behavior.Job.JobType} [inst : DecidableEq Job] {Task : Prosa.Model.Task.Concept.TaskType}
  [inst_1 : DecidableEq Task] [inst_2 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_3 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] [inst_4 : Prosa.Model.Task.Concept.TaskDeadline Task]
  [inst_5 : Prosa.Model.Task.Preemption.Parameters.TaskMaxNonpreemptiveSegment Task]
  [inst_6 : Prosa.Model.Task.Concept.JobTask Job Task] [inst_7 : Prosa.Behavior.Job.JobCost Job]
  [inst_8 : Prosa.Behavior.Job.JobArrival Job] {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (sched : Prosa.Behavior.Schedule.schedule PState),
      Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
        ∀ [inst_9 : Prosa.Model.Preemption.Parameter.JobPreemptable Job],
          Prosa.Model.Task.Preemption.Parameters.valid_model_with_bounded_nonpreemptive_segments arr_seq sched →
            ∀ (ts : List Task),
              Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
                ∀ (tsk : Task),
                  decide (tsk ∈ ts) = true →
                    Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
                      ∀ (j : Job),
                        Prosa.Model.Task.Concept.job_of_task tsk j = true →
                          ∀ (t1 t2 : Prosa.Behavior.Time.instant),
                            Prosa.Analysis.Definitions.BusyInterval.Classical.busy_interval_prefix arr_seq sched j t1
                                t2 →
                              Prosa.Analysis.Facts.BusyInterval.Pi.max_lp_nonpreemptive_segment arr_seq j t1 ≤
                                Prosa.Analysis.Definitions.BlockingBound.Edf.blocking_bound ts tsk
                                  (Prosa.Behavior.Job.job_arrival j - t1)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_BlockingBound_Edf_nonpreemptive_segments_bounded_by_blocking
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job)
         (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_7 : DecidableEq Task)
         (inst_10 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_7)
         (inst_13 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_7)
         (inst_16 : 
          Prosa_Model_Task_Concept_TaskDeadline Task
            inst_7)
         (inst_19 : 
          Prosa_Model_Task_Preemption_Parameters_TaskMaxNonpreemptiveSegment Task
            inst_7)
         (inst_22 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_3 Task
            inst_7)
         (inst_26 : 
          Prosa_Behavior_Job_JobCost Job
            inst_3)
         (inst_29 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_3)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_3),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_3
         inst_29 arr_seq ->
       forall
         sched : Prosa_Behavior_Schedule_schedule Job
                   inst_3 PState,
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_7
         inst_10 Job
         inst_3
         inst_22
         inst_26 arr_seq ->
       forall
         inst_51 : 
          Prosa_Model_Preemption_Parameter_JobPreemptable Job
            inst_3,
       Prosa_Model_Task_Preemption_Parameters_valid_model_with_bounded_nonpreemptive_segments Task
         inst_7 Job
         inst_3
         inst_22
         inst_26
         inst_19
         inst_51 PState arr_seq sched ->
       forall ts : List Task,
       Prosa_Model_Task_Concept_all_jobs_from_taskset Task
         inst_7 Job
         inst_3
         inst_22 arr_seq ts ->
       forall tsk : Task,
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task
                  inst_7)
               (instLawfulBEq Task
                  inst_7)
               tsk ts))
         Bool_true ->
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_7 Job
         inst_3
         inst_22 arr_seq
         inst_13 ts ->
       forall j : Job,
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_3 Task
            inst_7
            inst_22 tsk j)
         Bool_true ->
       forall t1 t2 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Definitions_BusyInterval_Classical_busy_interval_prefix Job
         inst_3
         inst_29
         inst_26 PState arr_seq sched
         (Prosa_Model_Priority_Edf_EDF Job
            inst_3
            (Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline Job Task
               inst_3
               inst_7
               inst_16
               inst_29
               inst_22))
         j t1 t2 ->
       LE_le_inst1 Nat instLENat
         (Prosa_Analysis_Facts_BusyInterval_Pi_max_lp_nonpreemptive_segment Job
            inst_3
            inst_26 arr_seq
            (Prosa_Model_Priority_Edf_EDF Job
               inst_3
               (Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline Job Task
                  inst_3
                  inst_7
                  inst_16
                  inst_29
                  inst_22))
            inst_51 j t1)
         (Prosa_Analysis_Definitions_BlockingBound_Edf_blocking_bound Task
            inst_7
            inst_10
            inst_16
            inst_19 ts
            inst_13 tsk
            (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
               Prosa_Behavior_Time_instant (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
               (Prosa_Behavior_Job_JobArrival_job_arrival Job
                  inst_3
                  inst_29 j)
               t1))
```
