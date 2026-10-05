# `non_pathological_max_arrivals`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.facts.model.arrival_curves.non_pathological_max_arrivals`
- Lean: `Prosa.Analysis.Facts.Model.ArrivalCurves.non_pathological_max_arrivals`
- Certificate: `non_pathological_max_arrivals_correspondence`

## Official Rocq

```coq
non_pathological_max_arrivals :
forall {Task : TaskType} {H : MaxArrivals Task} {Job : JobType} {H0 : JobTask Job Task}
  (tsk : Equality.sort Task) (arr_seq : arrival_sequence Job),
@respects_max_arrivals Task Job H0 arr_seq tsk (@max_arrivals Task H tsk) ->
forall j : Equality.sort Job,
is_true (@job_of_task Job Task H0 tsk j) ->
@arrives_in Job arr_seq j -> is_true (0 < @max_arrivals Task H tsk 1)

non_pathological_max_arrivals is not universe polymorphic
Arguments non_pathological_max_arrivals {Task H Job H0} tsk arr_seq H_curve_is_valid j H_job_of_tsk H_arrives
non_pathological_max_arrivals is opaque
Expands to: Constant prosa.analysis.facts.model.arrival_curves.non_pathological_max_arrivals
Declared in library prosa.analysis.facts.model.arrival_curves, line 36, characters 8-37
@non_pathological_max_arrivals
     : forall (Task : TaskType) (H : MaxArrivals Task) (Job : JobType) (H0 : JobTask Job Task)
         (tsk : Equality.sort Task) (arr_seq : arrival_sequence Job),
       @respects_max_arrivals Task Job H0 arr_seq tsk (@max_arrivals Task H tsk) ->
       forall j : Equality.sort Job,
       is_true (@job_of_task Job Task H0 tsk j) ->
       @arrives_in Job arr_seq j -> is_true (0 < @max_arrivals Task H tsk 1)
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.ArrivalCurves.non_pathological_max_arrivals : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] [inst_1 : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task]
  {Job : Prosa.Behavior.Job.JobType} [inst_2 : DecidableEq Job] [inst_3 : Prosa.Model.Task.Concept.JobTask Job Task]
  (tsk : Task) (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Model.Task.Arrival.Curves.respects_max_arrivals arr_seq tsk (Prosa.Model.Task.Arrival.Curves.max_arrivals tsk) →
    ∀ (j : Job),
      Prosa.Model.Task.Concept.job_of_task tsk j = true →
        Prosa.Behavior.Arrival_sequence.arrives_in arr_seq j → 0 < Prosa.Model.Task.Arrival.Curves.max_arrivals tsk 1
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_ArrivalCurves_non_pathological_max_arrivals
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
         (tsk : Task)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_10),
       Prosa_Model_Task_Arrival_Curves_respects_max_arrivals Task
         inst_3 Job
         inst_10
         inst_13 arr_seq tsk
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_6 tsk) ->
       forall j : Job,
       @eq Bool
         (Prosa_Model_Task_Concept_job_of_task Job
            inst_10 Task
            inst_3
            inst_13 tsk j)
         Bool_true ->
       Prosa_Behavior_Arrival_sequence_arrives_in Job
         inst_10 arr_seq j ->
       LT_lt_inst1 Nat instLTNat (OfNat_ofNat_inst1 Nat 0 (instOfNatNat 0))
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3
            inst_6 tsk
            (OfNat_ofNat_inst1 Prosa_Behavior_Time_duration 1 (instOfNatNat 1)))
```
