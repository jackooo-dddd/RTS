# `fp_hep_arrivals_bounded_by_sum_max_arrivals`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.arrival_curves.fp_hep_arrivals_bounded_by_sum_max_arrivals`
- Lean: `Prosa.Analysis.Facts.Model.ArrivalCurves.fp_hep_arrivals_bounded_by_sum_max_arrivals`
- Certificate: `fp_hep_arrivals_bounded_by_sum_max_arrivals_correspondence`

## Official Rocq

```coq
fp_hep_arrivals_bounded_by_sum_max_arrivals :
forall {Task : TaskType} {H : MaxArrivals Task} {Job : JobType} {H0 : JobTask Job Task} 
  {H2 : FP_policy Task} (arr_seq : arrival_sequence Job) (ts : seq (Equality.sort Task)),
@all_jobs_from_taskset Task Job H0 arr_seq ts ->
@taskset_respects_max_arrivals Task Job H0 arr_seq H ts ->
forall (j : Equality.sort Job) (t1 : instant) (Δ : duration),
is_true
  (@size (Equality.sort Job)
     [seq jhp <- @arrivals_between Job arr_seq t1 (t1 + Δ) | @hep_job Job (@FP_to_JLFP Job Task H0 H2) jhp j] <=
   \sum_(tsk <- ts | @hep_task Task H2 tsk (@job_task Job Task H0 j)) @max_arrivals Task H tsk Δ)

fp_hep_arrivals_bounded_by_sum_max_arrivals is not universe polymorphic
Arguments fp_hep_arrivals_bounded_by_sum_max_arrivals {Task H Job H0 H2} arr_seq 
  ts%seq_scope H_all_jobs_from_taskset H_is_arrival_curve j t1 Δ
fp_hep_arrivals_bounded_by_sum_max_arrivals is opaque
Expands to: Constant prosa.analysis.facts.model.arrival_curves.fp_hep_arrivals_bounded_by_sum_max_arrivals
Declared in library prosa.analysis.facts.model.arrival_curves, line 149, characters 8-51
@fp_hep_arrivals_bounded_by_sum_max_arrivals
     : forall (Task : TaskType) (H : MaxArrivals Task) (Job : JobType) (H0 : JobTask Job Task)
         (H2 : FP_policy Task) (arr_seq : arrival_sequence Job) (ts : seq (Equality.sort Task)),
       @all_jobs_from_taskset Task Job H0 arr_seq ts ->
       @taskset_respects_max_arrivals Task Job H0 arr_seq H ts ->
       forall (j : Equality.sort Job) (t1 : instant) (Δ : duration),
       is_true
         (@size (Equality.sort Job)
            [seq jhp <- @arrivals_between Job arr_seq t1 (t1 + Δ)
               | @hep_job Job (@FP_to_JLFP Job Task H0 H2) jhp j] <=
          \sum_(tsk <- ts | @hep_task Task H2 tsk (@job_task Job Task H0 j)) @max_arrivals Task H tsk Δ)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.ArrivalCurves.fp_hep_arrivals_bounded_by_sum_max_arrivals : ∀
  {Task : Prosa.Model.Task.Concept.TaskType} [inst : DecidableEq Task]
  [inst_1 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] {Job : Prosa.Behavior.Job.JobType}
  [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  [FP : Prosa.Model.Priority.Definitions.FP_policy Task]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job) (ts : List Task),
  Prosa.Model.Task.Concept.all_jobs_from_taskset arr_seq ts →
    Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
      ∀ (j : Job) (t1 : Prosa.Behavior.Time.instant) (Δ : Prosa.Behavior.Time.duration),
        (List.filter (fun jhp => Prosa.Model.Priority.Definitions.hep_job jhp j)
              (Prosa.Behavior.Arrival_sequence.arrivals_between arr_seq t1 (t1 + Δ))).length ≤
          Prosa.Util.Sum.sumFiltered ts
            (fun tsk => Prosa.Model.Priority.Definitions.hep_task tsk (Prosa.Model.Task.Concept.job_task j)) fun tsk =>
            Prosa.Model.Task.Arrival.Curves.max_arrivals tsk Δ
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_ArrivalCurves_fp_hep_arrivals_bounded_by_sum_max_arrivals
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (inst_6 : 
          Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
            inst_3)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_10 : DecidableEq Job)
         (inst_13 : 
          Prosa_Model_Task_Concept_JobTask Job
            inst_10 Task
            inst_3)
         (FP : Prosa_Model_Priority_Definitions_FP_policy Task
                 inst_3)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_10)
         (ts : List Task),
       Prosa_Model_Task_Concept_all_jobs_from_taskset Task
         inst_3 Job
         inst_10
         inst_13 arr_seq ts ->
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_10
         inst_13 arr_seq
         inst_6 ts ->
       forall (j : Job) (t1 : Prosa_Behavior_Time_instant) (_UU0394_ : Prosa_Behavior_Time_duration),
       LE_le_inst1 Nat instLENat
         (List_length Job
            (List_filter Job
               (fun jhp : Job =>
                Prosa_Model_Priority_Definitions_JLFP_policy_hep_job Job
                  inst_10
                  (Prosa_Model_Priority_Coercion_FP_to_JLFP Job
                     inst_10 Task
                     inst_3
                     inst_13 FP)
                  jhp j)
               (Prosa_Behavior_Arrival_sequence_arrivals_between Job
                  inst_10 arr_seq t1
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_instant (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat) t1
                     _UU0394_))))
         (Prosa_Util_Sum_sumFiltered Task ts
            (fun tsk : Task =>
             Prosa_Model_Priority_Definitions_FP_policy_hep_task Task
               inst_3 FP tsk
               (Prosa_Model_Task_Concept_JobTask_job_task Job
                  inst_10 Task
                  inst_3
                  inst_13 j))
            (fun tsk : Task =>
             Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
               inst_3
               inst_6 tsk _UU0394_))
```
