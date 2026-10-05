# `pathological_rbf_response_time_bound`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.rbf.pathological_rbf_response_time_bound`
- Lean: `Prosa.Analysis.Facts.Model.Rbf.pathological_rbf_response_time_bound`
- Certificate: `pathological_rbf_response_time_bound_correspondence`

## Official Rocq

```coq
pathological_rbf_response_time_bound :
forall {Task : TaskType} {H : TaskCost Task} {H0 : MaxArrivals Task} (ts : seq (Equality.sort Task))
  {Job : JobType} {H1 : JobTask Job Task} {H2 : JobArrival Job} {H3 : JobCost Job}
  (arr_seq : arrival_sequence Job),
@arrivals_have_valid_job_costs Task H Job H1 H3 arr_seq ->
@taskset_respects_max_arrivals Task Job H1 arr_seq H0 ts ->
forall {PState : ProcessorState Job} (sched : @schedule Job PState) (tsk : Equality.sort Task),
is_true (tsk \in ts) ->
@task_request_bound_function Task H H0 tsk 1 = 0 ->
@task_response_time_bound Task Job H2 H3 H1 PState arr_seq sched tsk 0

pathological_rbf_response_time_bound is not universe polymorphic
Arguments pathological_rbf_response_time_bound {Task H H0} ts%seq_scope {Job H1 H2 H3} 
  arr_seq H_valid_job_cost H_is_arrival_curve {PState} sched tsk _ _ j _ _
pathological_rbf_response_time_bound is opaque
Expands to: Constant prosa.analysis.facts.model.rbf.pathological_rbf_response_time_bound
Declared in library prosa.analysis.facts.model.rbf, line 438, characters 8-44
@pathological_rbf_response_time_bound
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (ts : seq (Equality.sort Task))
         (Job : JobType) (H1 : JobTask Job Task) (H2 : JobArrival Job) (H3 : JobCost Job)
         (arr_seq : arrival_sequence Job),
       @arrivals_have_valid_job_costs Task H Job H1 H3 arr_seq ->
       @taskset_respects_max_arrivals Task Job H1 arr_seq H0 ts ->
       forall (PState : ProcessorState Job) (sched : @schedule Job PState) (tsk : Equality.sort Task),
       is_true (tsk \in ts) ->
       @task_request_bound_function Task H H0 tsk 1 = 0 ->
       @task_response_time_bound Task Job H2 H3 H1 PState arr_seq sched tsk 0
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Rbf.pathological_rbf_response_time_bound : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] (ts : List Task) {Job : Prosa.Behavior.Job.JobType}
  [inst_3 : DecidableEq Job] [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_5 : Prosa.Behavior.Job.JobArrival Job] [inst_6 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
    Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
      ∀ (PState : Prosa.Behavior.Schedule.ProcessorState Job) (sched : Prosa.Behavior.Schedule.schedule PState)
        (tsk : Task),
        decide (tsk ∈ ts) = true →
          Prosa.Analysis.Definitions.RequestBoundFunction.task_request_bound_function tsk 1 = 0 →
            Prosa.Analysis.Definitions.Schedulability.task_response_time_bound arr_seq sched tsk 0
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Rbf_pathological_rbf_response_time_bound
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : Prosa_Model_Task_Concept_TaskCost
                                                                                Task
                                                                                inst_3)
         (inst_9 : Prosa_Model_Task_Arrival_Curves_MaxArrivals
                                                                                Task
                                                                                inst_3)
         (ts : List Task) (Job : Prosa_Behavior_Job_JobType)
         (inst_15 : DecidableEq Job)
         (inst_18 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_15 Task
            inst_3)
         (inst_22 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_15)
         (inst_25 : 
          Prosa_Behavior_Job_JobCost Job inst_15)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_15),
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_6 Job
         inst_15
         inst_18
         inst_25 arr_seq ->
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_15
         inst_18 arr_seq
         inst_9 ts ->
       forall
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_15)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_15 PState)
         (tsk : Task),
       @eq Bool
         (Decidable_decide (Membership_mem Task (List Task) (List_instMembership Task) ts tsk)
            (List_instDecidableMemOfLawfulBEq Task
               (instBEqOfDecidableEq Task inst_3)
               (instLawfulBEq Task inst_3) tsk
               ts))
         Bool_true ->
       @eq Nat
         (Prosa_Analysis_Definitions_RequestBoundFunction_task_request_bound_function Task
            inst_3
            inst_6
            inst_9 tsk
            (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))
         (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0)) ->
       Prosa_Analysis_Definitions_Schedulability_task_response_time_bound Task
         inst_3 Job
         inst_15
         inst_22
         inst_25
         inst_18 PState arr_seq sched tsk
         (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 0 (instOfNatNat 0))
```
