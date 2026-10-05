# `release_curve_respected`

- Kind (Rocq): Corollary
- Rocq: `prosa.analysis.facts.jitter.release_curve_respected`
- Lean: `Prosa.Analysis.Facts.Jitter.release_curve_respected`
- Certificate: `release_curve_respected_correspondence`

## Official Rocq

```coq
release_curve_respected :
forall {Task : TaskType} {arrival_curve : MaxArrivals Task} {Job : JobType} {H : JobTask Job Task}
  {original_arrival : JobArrival Job} {H0 : TaskJitter Task} {H1 : JobJitter Job}
  (arr_seq : arrival_sequence Job),
@valid_arrival_sequence Job original_arrival arr_seq ->
forall ts : seq (Equality.sort Task),
@valid_jitter_bounds Task H0 Job H H1 ts ->
@valid_taskset_arrival_curve Task ts (@max_arrivals Task arrival_curve) ->
@taskset_respects_max_arrivals Task Job H arr_seq arrival_curve ts ->
@taskset_respects_max_arrivals Task Job H (@release_sequence Job original_arrival H1 arr_seq)
  (@release_curve Task arrival_curve H0) ts

release_curve_respected is not universe polymorphic
Arguments release_curve_respected {Task arrival_curve Job H original_arrival H0 H1} 
  arr_seq H_valid_arrival_sequence ts%seq_scope H_valid_jitter _ _ tsk _ t1 t2 _
release_curve_respected is opaque
Expands to: Constant prosa.analysis.facts.jitter.release_curve_respected
Declared in library prosa.analysis.facts.jitter, line 79, characters 12-35
@release_curve_respected
     : forall (Task : TaskType) (arrival_curve : MaxArrivals Task) (Job : JobType) 
         (H : JobTask Job Task) (original_arrival : JobArrival Job) (H0 : TaskJitter Task)
         (H1 : JobJitter Job) (arr_seq : arrival_sequence Job),
       @valid_arrival_sequence Job original_arrival arr_seq ->
       forall ts : seq (Equality.sort Task),
       @valid_jitter_bounds Task H0 Job H H1 ts ->
       @valid_taskset_arrival_curve Task ts (@max_arrivals Task arrival_curve) ->
       @taskset_respects_max_arrivals Task Job H arr_seq arrival_curve ts ->
       @taskset_respects_max_arrivals Task Job H (@release_sequence Job original_arrival H1 arr_seq)
         (@release_curve Task arrival_curve H0) ts
```

## Lean

```lean
@Prosa.Analysis.Facts.Jitter.release_curve_respected : ∀ {Task : Prosa.Model.Task.Concept.TaskType}
  [inst : DecidableEq Task] {Job : Prosa.Behavior.Job.JobType} [inst_1 : DecidableEq Job]
  (arrival_curve : Prosa.Model.Task.Arrival.Curves.MaxArrivals Task)
  [inst_2 : Prosa.Model.Task.Concept.JobTask Job Task] (original_arrival : Prosa.Behavior.Job.JobArrival Job)
  [inst_3 : Prosa.Model.Task.Jitter.TaskJitter Task] [inst_4 : Prosa.Model.Readiness.Jitter.JobJitter Job]
  (arr_seq : Prosa.Behavior.Arrival_sequence.arrival_sequence Job),
  Prosa.Behavior.Arrival_sequence.valid_arrival_sequence arr_seq →
    ∀ (ts : Prosa.Model.Task.Concept.TaskSet Task),
      Prosa.Model.Task.Jitter.valid_jitter_bounds ts →
        Prosa.Model.Task.Arrival.Curves.valid_taskset_arrival_curve ts Prosa.Model.Task.Arrival.Curves.max_arrivals →
          Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals arr_seq ts →
            Prosa.Model.Task.Arrival.Curves.taskset_respects_max_arrivals
              (Prosa.Analysis.Definitions.DelayPropagation.release_sequence original_arrival arr_seq) ts
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Jitter_release_curve_respected
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : DecidableEq Task)
         (Job : Prosa_Behavior_Job_JobType)
         (inst_7 : DecidableEq Job)
         (arrival_curve : Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
                            inst_3)
         (inst_12 : Prosa_Model_Task_Concept_JobTask
                                                                                Job
                                                                                inst_7
                                                                                Task
                                                                                inst_3)
         (original_arrival : Prosa_Behavior_Job_JobArrival Job
                               inst_7)
         (inst_18 : Prosa_Model_Task_Jitter_TaskJitter
                                                                                Task
                                                                                inst_3)
         (inst_21 : Prosa_Model_Readiness_Jitter_JobJitter
                                                                                Job
                                                                                inst_7)
         (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
                      inst_7),
       Prosa_Behavior_Arrival_sequence_valid_arrival_sequence Job
         inst_7 original_arrival arr_seq ->
       forall ts : Prosa_Model_Task_Concept_TaskSet Task,
       Prosa_Model_Task_Jitter_valid_jitter_bounds Task
         inst_3
         inst_18 Job
         inst_7
         inst_12
         inst_21 ts ->
       Prosa_Model_Task_Arrival_Curves_valid_taskset_arrival_curve Task
         inst_3 ts
         (Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
            inst_3 arrival_curve) ->
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_7
         inst_12 arr_seq arrival_curve ts ->
       Prosa_Model_Task_Arrival_Curves_taskset_respects_max_arrivals Task
         inst_3 Job
         inst_7
         inst_12
         (Prosa_Analysis_Definitions_DelayPropagation_release_sequence Job
            inst_7 original_arrival
            inst_21 arr_seq)
         (Prosa_Analysis_Facts_Jitter_release_curve Task
            inst_3 arrival_curve
            inst_18)
         ts
```
