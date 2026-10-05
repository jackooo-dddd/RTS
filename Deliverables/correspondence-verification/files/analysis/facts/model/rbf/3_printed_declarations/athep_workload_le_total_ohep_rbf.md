# `athep_workload_le_total_ohep_rbf`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.rbf.athep_workload_le_total_ohep_rbf`
- Lean: `Prosa.Analysis.Facts.Model.Rbf.athep_workload_le_total_ohep_rbf`
- Certificate: `athep_workload_le_total_ohep_rbf_correspondence`

## Official Rocq

```coq
athep_workload_le_total_ohep_rbf :
forall {Task : TaskType} {H : TaskCost Task} {H0 : MaxArrivals Task} {Job : JobType} 
  {H1 : JobTask Job Task} {H2 : JobArrival Job} {H3 : JobCost Job} (arr_seq : arrival_sequence Job)
  {PState : ProcessorState Job} (sched : @schedule Job PState),
@arrivals_have_valid_job_costs Task H Job H1 H3 arr_seq ->
forall ts : seq (Equality.sort Task),
@all_jobs_from_taskset Task Job H1 arr_seq ts ->
@taskset_respects_max_arrivals Task Job H1 arr_seq H0 ts ->
forall {FP : FP_policy Task} (tsk : Equality.sort Task),
@athep_workload_is_bounded Task Job H3 H2 H1 PState (@FP_to_JLFP Job Task H1 FP) arr_seq sched tsk
  (fun=> [eta @total_ohep_request_bound_function_FP Task H H0 ts FP tsk])

athep_workload_le_total_ohep_rbf is not universe polymorphic
Arguments athep_workload_le_total_ohep_rbf {Task H H0 Job H1 H2 H3} arr_seq {PState} 
  sched H_valid_job_cost ts%seq_scope H_all_jobs_from_taskset H_is_arrival_bound 
  {FP} tsk j t1 Δ _ _ _
athep_workload_le_total_ohep_rbf is opaque
Expands to: Constant prosa.analysis.facts.model.rbf.athep_workload_le_total_ohep_rbf
Declared in library prosa.analysis.facts.model.rbf, line 205, characters 10-42
@athep_workload_le_total_ohep_rbf
     : forall (Task : TaskType) (H : TaskCost Task) (H0 : MaxArrivals Task) (Job : JobType)
         (H1 : JobTask Job Task) (H2 : JobArrival Job) (H3 : JobCost Job) (arr_seq : arrival_sequence Job)
         (PState : ProcessorState Job) (sched : @schedule Job PState),
       @arrivals_have_valid_job_costs Task H Job H1 H3 arr_seq ->
       forall ts : seq (Equality.sort Task),
       @all_jobs_from_taskset Task Job H1 arr_seq ts ->
       @taskset_respects_max_arrivals Task Job H1 arr_seq H0 ts ->
       forall (FP : FP_policy Task) (tsk : Equality.sort Task),
       @athep_workload_is_bounded Task Job H3 H2 H1 PState (@FP_to_JLFP Job Task H1 FP) arr_seq sched tsk
         (fun=> [eta @total_ohep_request_bound_function_FP Task H H0 ts FP tsk])
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Rbf.athep_workload_le_total_ohep_rbf : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Concept.TaskCost Task]
  [inst_2 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_3 : DecidableEq Job] [inst_4 : Prosa.Model.Task.Concept.JobTask Job Task]
  [inst_5 : Prosa.Behavior.Job.JobArrival Job] [inst_6 : Prosa.Behavior.Job.JobCost Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) {PState : Prosa.Behavior.Schedule.ProcessorState Job}
  (sched : Prosa.Behavior.Schedule.schedule PState),
  Prosa.Model.Task.Concept.arrivals_have_valid_job_costs arr_seq →
    ∀ (ts : List Task),
      Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
        Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
          ∀ (FP : Prosa.Model.Priority.Definitions.FP_policy Task) (tsk : Task),
            Prosa.Analysis.Definitions.Workload.Bounded.athep_workload_is_bounded arr_seq sched tsk fun x Δ =>
              Prosa.Analysis.Definitions.RequestBoundFunction.total_ohep_request_bound_function_FP ts tsk Δ
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Rbf_athep_workload_le_total_ohep_rbf
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : Prosa_Model_Task_Concept_TaskCost
                                                                                Task
                                                                                inst_3)
         (inst_9 : Prosa_Model_Task_Arrival_Curves_MaxArrivals
                                                                                Task
                                                                                inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_13 : DecidableEq Job)
         (inst_16 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_13 Task
            inst_3)
         (inst_20 : 
          Prosa_Behavior_Job_JobArrival Job
            inst_13)
         (inst_23 : 
          Prosa_Behavior_Job_JobCost Job inst_13)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_13)
         (PState : Prosa_Behavior_Schedule_ProcessorState Job
                     inst_13)
         (sched : Prosa_Behavior_Schedule_schedule Job
                    inst_13 PState),
       Prosa_Model_Task_Concept_arrivals_have_valid_job_costs Task
         inst_3
         inst_6 Job
         inst_13
         inst_16
         inst_23 arr_seq ->
       forall ts : List Task,
       Prosa_Model_Task_Concept_all_jobs_from_taskset Task
         inst_3 Job
         inst_13
         inst_16 arr_seq ts ->
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_13
         inst_16 arr_seq
         inst_9 ts ->
       forall
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3)
         (tsk : Task),
       Prosa_Analysis_Definitions_Workload_Bounded_athep_workload_is_bounded Task
         inst_3 Job
         inst_13
         inst_23
         inst_20
         inst_16 PState
         (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
            inst_13 Task
            inst_3
            inst_16 FP)
         arr_seq sched tsk
         (fun _ _UU0394_ : Prosa_Behavior_Time_duration =>
          Prosa_Analysis_Definitions_RequestBoundFunction_total_ohep_request_bound_function_FP Task
            inst_3
            inst_6
            inst_9 ts FP tsk _UU0394_)
```
