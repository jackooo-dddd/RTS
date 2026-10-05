# `sum_of_workloads_is_at_most_bound_on_total_hep_workload`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.workload.edf_athep_bound.sum_of_workloads_is_at_most_bound_on_total_hep_workload`
- Lean: `Prosa.Analysis.Facts.Workload.EdfAthepBound.sum_of_workloads_is_at_most_bound_on_total_hep_workload`
- Certificate: `sum_of_workloads_is_at_most_bound_on_total_hep_workload_correspondence`

## Official Rocq

```coq
sum_of_workloads_is_at_most_bound_on_total_hep_workload :
forall {Task : TaskType} {H : TaskCost Task} {H0 : TaskDeadline Task} {H1 : MaxArrivals Task} 
  {Job : JobType} {H2 : JobTask Job Task} {H3 : JobArrival Job} {H4 : JobCost Job}
  (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H3 arr_seq ->
@arrivals_have_valid_job_costs Task H Job H2 H4 arr_seq ->
forall ts : seq (Equality.sort Task),
@taskset_respects_max_arrivals Task Job H2 arr_seq H1 ts ->
forall (tsk : Equality.sort Task) (j : Equality.sort Job),
is_true (@job_of_task Job Task H2 tsk j) ->
is_true (@job_cost_positive Job H4 j) ->
forall t1 t2 Δ : duration,
is_true (t1 + Δ < t2) ->
is_true
  (\sum_(tsk_o <- ts | tsk_o != tsk)
      @workload_of_jobs Job H4
        ((fun (tsk0 : Equality.sort Task) (jo : Equality.sort Job) =>
          @EDF Job (@job_deadline_from_task_deadline Job Task H0 H3 H2) jo j &&
          (@job_task Job Task H2 jo == tsk0)) tsk_o)
        (@arrivals_between Job arr_seq t1 (t1 + Δ)) <=
   @bound_on_athep_workload Task H H0 H1 ts tsk (@job_arrival Job H3 j - t1) Δ)

sum_of_workloads_is_at_most_bound_on_total_hep_workload is not universe polymorphic
Arguments sum_of_workloads_is_at_most_bound_on_total_hep_workload {Task H H0 H1 Job H2 H3 H4} 
  arr_seq H_valid_arrival_sequence H_valid_job_cost ts%seq_scope H_is_arrival_curve 
  tsk j H_job_of_tsk H_job_cost_positive t1 t2 Δ H_Δ_in_busy
sum_of_workloads_is_at_most_bound_on_total_hep_workload is opaque
Expands to: Constant
            prosa.analysis.facts.workload.edf_athep_bound.sum_of_workloads_is_at_most_bound_on_total_hep_workload
Declared in library prosa.analysis.facts.workload.edf_athep_bound, line 130, characters 14-69
@sum_of_workloads_is_at_most_bound_on_total_hep_workload
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : TaskDeadline Task) (H1 : MaxArrivals Task)
         (Job : JobType) (H2 : JobTask Job Task) (H3 : JobArrival Job) (H4 : JobCost Job)
         (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H3 arr_seq ->
       @arrivals_have_valid_job_costs Task H Job H2 H4 arr_seq ->
       forall ts : seq (Equality.sort Task),
       @taskset_respects_max_arrivals Task Job H2 arr_seq H1 ts ->
       forall (tsk : Equality.sort Task) (j : Equality.sort Job),
       is_true (@job_of_task Job Task H2 tsk j) ->
       is_true (@job_cost_positive Job H4 j) ->
       forall t1 t2 Δ : duration,
       is_true (t1 + Δ < t2) ->
       is_true
         (\sum_(tsk_o <- ts | tsk_o != tsk)
             @workload_of_jobs Job H4
               (fun jo : Equality.sort Job =>
                @EDF Job (@job_deadline_from_task_deadline Job Task H0 H3 H2) jo j &&
                (@job_task Job Task H2 jo == tsk_o))
               (@arrivals_between Job arr_seq t1 (t1 + Δ)) <=
          @bound_on_athep_workload Task H H0 H1 ts tsk (@job_arrival Job H3 j - t1) Δ)
```

## Lean

```lean
@Prosa.Analysis.Facts.Workload.EdfAthepBound.sum_of_workloads_is_at_most_bound_on_total_hep_workload : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Concept.TaskDeadline Task] [inst_3 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_4 : DecidableEq Job] [inst_5 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_6 : Prosa.Behavior.Job.JobArrival Job] [inst_7 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
      ∀ (ts : List Task),
        Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
          ∀ (tsk : Task) (j : Job),
            Prosa.Model.Task.Concept.job_of_task tsk j = true →
              Prosa.Model.Job.Properties.job_cost_positive j = true →
                ∀ (t1 t2 Δ : Prosa.Behavior.Time.duration),
                  t1 + Δ < t2 →
                    (Prosa.Util.Sum.sumFiltered ts (fun tsk_o => decide (tsk_o ≠ tsk)) fun tsk_o =>
                        Prosa.Model.Aggregate.Workload.workload_of_jobs
                          (fun jo =>
                            Prosa.Model.Priority.Definitions.hep_job jo j &&
                              decide (Prosa.Model.Task.Concept.job_task jo = tsk_o))
                          (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 (t1 + Δ))) ≤
                      Prosa.Analysis.Definitions.Workload.EdfAthepBound.bound_on_athep_workload ts tsk
                        (Prosa.Behavior.Job.job_arrival j - t1) Δ
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Workload_EdfAthepBound_sum_of_workloads_is_at_most_bound_on_total_hep_workload
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_9 : 
          Prosa_Model_Task_Concept_TaskDeadline Task
            inst_3)
         (inst_12 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_16 : 
          DecidableEq Job)
         (inst_19 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_16 Task
            inst_3)
         (inst_23 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_16)
         (inst_26 : 
          Prosa_Behavior_Job_JobCost Job
            inst_16)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_16),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_16
         inst_23 arr_seq ->
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_6 Job
         inst_16
         inst_19
         inst_26 arr_seq ->
       forall ts : List Task,
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_16
         inst_19 arr_seq
         inst_12 ts ->
       forall (tsk : Task) (j : Job),
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_16 Task
            inst_3
            inst_19 tsk j)
         Bool_true ->
       @eq Bool
         (Prosa_Model_Job_Properties_job_cost_positive Job
            inst_16
            inst_26 j)
         Bool_true ->
       forall t1 t2 _UU0394_ : Prosa_Behavior_Time_duration,
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) t1 _UU0394_)
         t2 ->
       LE_le_inst1 Nat instLENat
         (Prosa_Util_Sum_sumFiltered Task ts
            (fun tsk_o : Task =>
             Decidable_decide (Ne Task tsk_o tsk)
               (instDecidableNot (@eq Task tsk_o tsk)
                  (inst_3 tsk_o tsk)))
            (fun tsk_o : Task =>
             Prosa_Model_Aggregate_Workload_workload_of_jobs Job
               inst_16
               inst_26
               (fun jo : Job =>
                Bool_and
                  (Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
                     inst_16
                     (Prosa_Model_Priority_Edf_EDF Job
                        inst_16
                        (Prosa_Model_Task_AbsoluteDeadline_job_deadline_from_task_deadline Job Task
                           inst_16
                           inst_3
                           inst_9
                           inst_23
                           inst_19))
                     jo j)
                  (Decidable_decide
                     (@eq Task
                        (Prosa_Model_Task_Concept_JobTask_job_task Job
                           inst_16
                           Task
                           inst_3
                           inst_19
                           jo)
                        tsk_o)
                     (inst_3
                        (Prosa_Model_Task_Concept_JobTask_job_task Job
                           inst_16
                           Task
                           inst_3
                           inst_19
                           jo)
                        tsk_o)))
               (Prosa_Behavior_Arrival_sequence_arrivals_between Job
                  inst_16 arr_seq
                  t1
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) t1
                     _UU0394_))))
         (Prosa_Analysis_Definitions_Workload_EdfAthepBound_bound_on_athep_workload Task
            inst_3
            inst_6
            inst_9
            inst_12 ts tsk
            (HSub_hSub_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_instant (instHSub_inst1 Prosa_Behavior_Time_instant instSubNat)
               (Prosa_Behavior_Job_JobArrival_job_arrival Job
                  inst_16
                  inst_23 j)
               t1)
            _UU0394_)
```
