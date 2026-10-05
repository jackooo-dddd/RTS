# `busy_interval_has_uninterrupted_service`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.busy_interval.busy_interval_has_uninterrupted_service`
- Lean: `Prosa.Analysis.Abstract.BusyInterval.busy_interval_has_uninterrupted_service`
- Certificate: `busy_interval_has_uninterrupted_service_correspondence`

## Official Rocq

```coq
busy_interval_has_uninterrupted_service :
forall {Task : TaskType} {Job : JobType} {H0 : JobTask Job Task} {H1 : JobArrival Job} 
  {H2 : JobCost Job} {PState : ProcessorState Job} {H3 : Interference Job} {H4 : InterferingWorkload Job}
  (arr_seq : arrival_sequence Job) (tsk : Equality.sort Task) (sched : @schedule Job PState),
@work_conserving Job H1 H2 PState arr_seq sched H3 H4 ->
forall j : Equality.sort Job,
@arrives_in Job arr_seq j ->
is_true (@job_of_task Job Task H0 tsk j) ->
is_true (@job_cost_positive Job H2 j) ->
forall t_busy t1 : instant,
@busy_interval_prefix Job H1 H2 PState sched H3 H4 j t1 t_busy.+1 ->
forall δ : duration,
(forall t : nat, is_true (t1 < t <= t1 + δ) -> ~ is_true ([eta @quiet_time Job H1 H2 PState sched H3 H4 j] t)) ->
is_true (δ <= @service_during Job PState sched j t1 (t1 + δ) + @cumulative_interference Job H3 j t1 (t1 + δ))

busy_interval_has_uninterrupted_service is not universe polymorphic
Arguments busy_interval_has_uninterrupted_service {Task Job H0 H1 H2 PState H3 H4} 
  arr_seq tsk sched H_work_conserving j H_from_arrival_sequence H_job_task H_job_cost_positive 
  t_busy t1 H_is_busy_prefix δ H_no_quiet_time%function_scope
busy_interval_has_uninterrupted_service is opaque
Expands to: Constant prosa.analysis.abstract.busy_interval.busy_interval_has_uninterrupted_service
Declared in library prosa.analysis.abstract.busy_interval, line 393, characters 14-53
@busy_interval_has_uninterrupted_service
     : forall (Task : TaskType) (Job : JobType) (H0 : JobTask Job Task) (H1 : JobArrival Job)
         (H2 : JobCost Job) (PState : ProcessorState Job) (H3 : Interference Job)
         (H4 : InterferingWorkload Job) (arr_seq : arrival_sequence Job) (tsk : Equality.sort Task)
         (sched : @schedule Job PState),
       @work_conserving Job H1 H2 PState arr_seq sched H3 H4 ->
       forall j : Equality.sort Job,
       @arrives_in Job arr_seq j ->
       is_true (@job_of_task Job Task H0 tsk j) ->
       is_true (@job_cost_positive Job H2 j) ->
       forall t_busy t1 : instant,
       @busy_interval_prefix Job H1 H2 PState sched H3 H4 j t1 t_busy.+1 ->
       forall δ : duration,
       (forall t : nat,
        is_true (t1 < t <= t1 + δ) -> ~ is_true (@quiet_time Job H1 H2 PState sched H3 H4 j t)) ->
       is_true
         (δ <= @service_during Job PState sched j t1 (t1 + δ) + @cumulative_interference Job H3 j t1 (t1 + δ))
```

## Lean

```lean
@Prosa.Analysis.Abstract.BusyInterval.busy_interval_has_uninterrupted_service : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_1 : DecidableEq Job] [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_3 : Prosa.Behavior.Job.JobArrival Job] [inst_4 : Prosa.Behavior.Job.JobCost Job]
  {PState : Prosa.Behavior.Schedule.ProcessorState Job} [inst_5 : Prosa.Analysis.Abstract.Definitions.Interference Job]
  [inst_6 : Prosa.Analysis.Abstract.Definitions.InterferingWorkload Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (tsk : Task)
  (sched : Prosa.Behavior.Schedule.schedule PState),
  Prosa.Analysis.Abstract.Definitions.work_conserving arr_seq sched →
    ∀ (j : Job),
      Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j →
        Prosa.Model.Task.Concept.job_of_task tsk j = true →
          Prosa.Model.Job.Properties.job_cost_positive j = true →
            ∀ (t_busy t1 : Prosa.Behavior.Time.instant),
              Prosa.Analysis.Abstract.Definitions.busy_interval_prefix sched j t1 (t_busy + 1) →
                ∀ (δ : Prosa.Behavior.Time.duration),
                  (∀ (t : ℕ),
                      (decide (t1 < t) && decide (t ≤ t1 + δ)) = true →
                        ¬Prosa.Analysis.Abstract.Definitions.quiet_time sched j t = true) →
                    δ ≤
                      Prosa.Behavior.Service.service_during sched j t1 (t1 + δ) +
                        Prosa.Analysis.Abstract.Definitions.cumulative_interference j t1 (t1 + δ)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_BusyInterval_busy_interval_has_uninterrupted_service
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (inst_10 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_7 Task
            inst_3)
         (inst_14 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_7)
         (inst_17 : 
          Prosa_Behavior_Job_JobCost Job
            inst_7)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_7)
         (inst_22 : 
          Prosa_Analysis_Abstract_Definitions_Interference Job
            inst_7)
         (inst_25 : 
          Prosa_Analysis_Abstract_Definitions_InterferingWorkload Job
            inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7)
         (tsk : Task)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_7 PState),
       Prosa_Analysis_Abstract_Definitions_work_conserving Job
         inst_7
         inst_22
         inst_25
         inst_14
         inst_17 PState arr_seq sched ->
       forall j : Job,
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_7 arr_seq j ->
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_7 Task
            inst_3
            inst_10 tsk j)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_7
            inst_17 j)
         Bool_true ->
       forall t_busy t1 : Prosa_Behavior_Time_instant,
       Prosa_Analysis_Abstract_Definitions_busy_interval_prefix Job
         inst_7
         inst_22
         inst_25
         inst_14
         inst_17 PState sched j t1
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant Prosa_Behavior_Time_instant
            (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t_busy
            (OfNat_ofNat_inst1 Prosa_Behavior_Time_instant 1 (instOfNatNat 1))) ->
       forall _UU03b4_ : Prosa_Behavior_Time_duration,
       (forall t : Nat,
        @eq Bool
          (Bool_and
             (Decidable_decide (LT_lt_inst1 Prosa_Behavior_Time_instant instLTNat t1 t) (Nat_decLt t1 t))
             (Decidable_decide
                (LE_le_inst1 Nat instLENat t
                   (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                      Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                      _UU03b4_))
                (Nat_decLe t
                   (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                      Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                      _UU03b4_))))
          Bool_true ->
        Not
          (@eq Bool
             (Prosa_Analysis_Abstract_Definitions_quiet_time Job
                inst_7
                inst_22
                inst_25
                inst_14
                inst_17 PState sched j t)
             Bool_true)) ->
       LE_le_inst1 Prosa_Behavior_Time_duration instLENat _UU03b4_
         (HAdd_hAdd_inst7 Prosa_Behavior_Job_work Nat Prosa_Behavior_Job_work
            (instHAdd_inst1 Prosa_Behavior_Job_work instAddNat)
            (Prosa_Behavior_Service_service_during Job
               inst_7 PState sched j t1
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                  _UU03b4_))
            (Prosa_Analysis_Abstract_Definitions_cumulative_interference Job
               inst_7
               inst_22 j t1
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                  _UU03b4_)))
```
