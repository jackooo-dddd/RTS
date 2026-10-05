# `task_demand_within_le_task_rbf_shifted`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.model.dbf.task_demand_within_le_task_rbf_shifted`
- Lean: `Prosa.Analysis.Facts.Model.Dbf.task_demand_within_le_task_rbf_shifted`
- Certificate: `task_demand_within_le_task_rbf_shifted_correspondence`

## Official Rocq

```coq
task_demand_within_le_task_rbf_shifted :
forall {Task : TaskType} {H : TaskDeadline Task} {Job : JobType} {H0 : JobTask Job Task}
  {H1 : JobArrival Job} (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job H1 arr_seq ->
forall {H2 : TaskCost Task} {H3 : JobCost Job},
@arrivals_have_valid_job_costs Task H2 Job H0 H3 arr_seq ->
forall (ts : seq (Equality.sort Task)) {H4 : MaxArrivals Task},
@taskset_respects_max_arrivals Task Job H0 arr_seq H4 ts ->
forall (tsk : Equality.sort Task) (t : instant) (delta : nat),
is_true (tsk \in ts) ->
is_true
  (@task_demand_within Task H Job H0 H1 arr_seq H3 tsk t (t + delta) <=
   @task_request_bound_function Task H2 H4 tsk (delta - (@task_deadline Task H tsk - 1)))

task_demand_within_le_task_rbf_shifted is not universe polymorphic
Arguments task_demand_within_le_task_rbf_shifted {Task H Job H0 H1} arr_seq H_valid_arrival_sequence 
  {H2 H3} H_valid_job_cost ts%seq_scope {H4} H_is_arrival_bound tsk t delta%nat_scope 
  _
task_demand_within_le_task_rbf_shifted is opaque
Expands to: Constant prosa.analysis.facts.model.dbf.task_demand_within_le_task_rbf_shifted
Declared in library prosa.analysis.facts.model.dbf, line 102, characters 12-50
@task_demand_within_le_task_rbf_shifted
     : forall (Task : TaskType) (H : TaskDeadline Task) (Job : JobType) (H0 : JobTask Job Task)
         (H1 : JobArrival Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job H1 arr_seq ->
       forall (H2 : TaskCost Task) (H3 : JobCost Job),
       @arrivals_have_valid_job_costs Task H2 Job H0 H3 arr_seq ->
       forall (ts : seq (Equality.sort Task)) (H4 : MaxArrivals Task),
       @taskset_respects_max_arrivals Task Job H0 arr_seq H4 ts ->
       forall (tsk : Equality.sort Task) (t : instant) (delta : nat),
       is_true (tsk \in ts) ->
       is_true
         (@task_demand_within Task H Job H0 H1 arr_seq H3 tsk t (t + delta) <=
          @task_request_bound_function Task H2 H4 tsk (delta - (@task_deadline Task H tsk - 1)))
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Dbf.task_demand_within_le_task_rbf_shifted : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskDeadline Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_4 : Prosa.Behavior.Job.JobArrival Job] (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ [inst_5 : Prosa.Model.Task.Concept.TaskCost Task] [inst_6 : Prosa.Behavior.Job.JobCost Job],
      Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
        ∀ (ts : List Task) [inst_7 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task],
          Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
            ∀ (tsk : Task) (t : Prosa.Behavior.Time.instant) (delta : ℕ),
              decide (tsk ∈ ts) = true →
                Prosa.Analysis.Facts.Model.Dbf.task_demand_within arr_seq tsk t (t + delta) ≤
                  Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk
                    (delta - (Prosa.Model.Task.Concept.task_deadline tsk - 1))
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Dbf_task_demand_within_le_task_rbf_shifted
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : Prosa_Model_Task_Concept_TaskDeadline
                                                                                Task
                                                                                inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job)
         (inst_13 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_10 Task
            inst_3)
         (inst_17 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_10)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_10),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_10
         inst_17 arr_seq ->
       forall
         (inst_27 : 
          Prosa_Model_Task_Concept_TaskCost Task
            inst_3)
         (inst_30 : 
          Prosa_Behavior_Job_JobCost Job inst_10),
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_27 Job
         inst_10
         inst_13
         inst_30 arr_seq ->
       forall (ts : List Task)
         (inst_41 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3),
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_10
         inst_13 arr_seq
         inst_41 ts ->
       forall (tsk : Task) (t : Prosa_Behavior_Time_instant) (delta : Nat),
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task inst_3)
               (instLawfulBEq Task inst_3) tsk
               ts))
         Bool_true ->
       LE_le_inst1 Nat instLENat
         (Prosa_Analysis_Facts_Model_Dbf_task_demand_within Task
            inst_3
            inst_6 Job
            inst_10
            inst_13
            inst_17 arr_seq
            inst_30 tsk t
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Nat Prosa_Behavior_Time_instant
               (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t delta))
         (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
            inst_3
            inst_27
            inst_41 tsk
            (HSub_hSub_inst7 Nat Prosa_Behavior_Time_duration Nat (instHSub_inst1 Nat instSubNat) delta
               (HSub_hSub_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_duration (instHSub_inst1 Prosa_Behavior_Time_duration instSubNat)
                  (Prosa_Model_Task_Concept_TaskDeadline_task_deadline Task
                     inst_3
                     inst_6 tsk)
                  (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))))
```
