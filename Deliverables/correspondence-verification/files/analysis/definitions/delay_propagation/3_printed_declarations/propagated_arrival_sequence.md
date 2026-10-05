# `propagated_arrival_sequence`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.delay_propagation.propagated_arrival_sequence`
- Lean: `Prosa.Analysis.Definitions.DelayPropagation.propagated_arrival_sequence`
- Certificate: `propagated_arrival_sequence_correspondence`

## Official Rocq

```coq
propagated_arrival_sequence :
forall {Job1 Job2 : JobType},
JobArrival Job1 ->
(Equality.sort Job2 -> Equality.sort Job1) ->
arrival_sequence Job1 ->
(Equality.sort Job1 -> seq (Equality.sort Job2)) ->
(Equality.sort Job2 -> duration) -> instant -> seq (Equality.sort Job2)

propagated_arrival_sequence is not universe polymorphic
Arguments propagated_arrival_sequence {Job1 Job2} H1 job1_of%function_scope arr_seq1
  (job2_of arrival_delay)%function_scope t
propagated_arrival_sequence is transparent
Expands to: Constant prosa.analysis.definitions.delay_propagation.propagated_arrival_sequence
Declared in library prosa.analysis.definitions.delay_propagation, line 91, characters 13-40
@propagated_arrival_sequence
     : forall Job1 Job2 : JobType,
       JobArrival Job1 ->
       (Equality.sort Job2 -> Equality.sort Job1) ->
       arrival_sequence Job1 ->
       (Equality.sort Job1 -> seq (Equality.sort Job2)) ->
       (Equality.sort Job2 -> duration) -> instant -> seq (Equality.sort Job2)
```

Body:

```coq
propagated_arrival_sequence =
fun (Job1 Job2 : JobType) (H1 : JobArrival Job1) (job1_of : Equality.sort Job2 -> Equality.sort Job1)
  (arr_seq1 : arrival_sequence Job1) (job2_of : Equality.sort Job1 -> seq (Equality.sort Job2))
  (arrival_delay : Equality.sort Job2 -> duration) (t : instant) =>
let all := [seq job2_of j | j <- @arrivals_up_to Job1 arr_seq1 t] in
     : forall {Job1 Job2 : JobType},
       JobArrival Job1 ->
       (Equality.sort Job2 -> Equality.sort Job1) ->
       arrival_sequence Job1 ->
       (Equality.sort Job1 -> seq (Equality.sort Job2)) ->
       (Equality.sort Job2 -> duration) -> instant -> seq (Equality.sort Job2)

Arguments propagated_arrival_sequence {Job1 Job2} H1 job1_of%function_scope arr_seq1
  (job2_of arrival_delay)%function_scope t
```

## Lean

```lean
@Prosa.Analysis.Definitions.DelayPropagation.propagated_arrival_sequence : {Job1 : Prosa.Behavior.Job.JobType} →
  {Job2 : Prosa.Behavior.Job.JobType} →
    [inst : DecidableEq Job1] →
      [DecidableEq Job2] →
        Prosa.Behavior.Job.JobArrival Job1 →
          (Job2 → Job1) →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job1 →
              (Job1 → List Job2) → (Job2 → Prosa.Behavior.Time.duration) → Prosa.Behavior.Time.instant → List Job2
def Prosa.Analysis.Definitions.DelayPropagation.propagated_arrival_sequence.{u_1, u_2} : {Job1 :
    Prosa.Behavior.Job.JobType} →
  {Job2 : Prosa.Behavior.Job.JobType} →
    [inst : DecidableEq Job1] →
      [DecidableEq Job2] →
        Prosa.Behavior.Job.JobArrival Job1 →
          (Job2 → Job1) →
            Prosa.Behavior.Arrival_sequence.arrival_sequence Job1 →
              (Job1 → List Job2) → (Job2 → Prosa.Behavior.Time.duration) → Prosa.Behavior.Time.instant → List Job2 :=
fun {Job1} {Job2} [DecidableEq Job1] [DecidableEq Job2] ja1 job1_of arr_seq1 job2_of arrival_delay t =>
  List.filter (fun j2 => decide (Prosa.Behavior.Job.job_arrival (job1_of j2) + arrival_delay j2 = t))
    (List.map job2_of (Prosa.Behavior.Arrival_sequence.arrivals_up_to arr_seq1 t)).flatten
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_DelayPropagation_propagated_arrival_sequence
     : forall (Job1 Job2 : Prosa_Behavior_Job_JobType)
         (inst_4 : 
          DecidableEq Job1),
       DecidableEq Job2 ->
       Prosa_Behavior_Job_JobArrival Job1
         inst_4 ->
       (Job2 -> Job1) ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job1
         inst_4 ->
       (Job1 -> List Job2) ->
       (Job2 -> Prosa_Behavior_Time_duration) -> Prosa_Behavior_Time_instant -> List Job2
```

Body:

```coq
Prosa_Analysis_Definitions_DelayPropagation_propagated_arrival_sequence@{u_1 u_2 Lean.u_1+1.0
Lean.max__u_1+1_u_2+1.0 Lean.u_2+1.0 Lean.u_1+2.0 Lean.max__u_1+2_u_2+2.0 Lean.u_2+2.0} =
fun (Job1 Job2 : Prosa_Behavior_Job_JobType)
  (inst_4 : DecidableEq Job1)
  (_ : DecidableEq Job2)
  (ja1 : Prosa_Behavior_Job_JobArrival Job1
           inst_4)
  (job1_of : Job2 -> Job1)
  (arr_seq1 : Prosa_Behavior_Arrival_sequence_arrival_sequence Job1
                inst_4)
  (job2_of : Job1 -> List Job2) (arrival_delay : Job2 -> Prosa_Behavior_Time_duration)
  (t : Prosa_Behavior_Time_instant) =>
List_filter Job2
  (fun j2 : Job2 =>
   Decidable_decide
     (@eq Prosa_Behavior_Time_instant
        (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration Prosa_Behavior_Time_instant
           (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
           (Prosa_Behavior_Job_JobArrival_job_arrival Job1
              inst_4 ja1
              (job1_of j2))
           (arrival_delay j2))
        t)
     (instDecidableEqNat
        (HAdd_hAdd_inst7 Prosa_Behavior_Time_instant Prosa_Behavior_Time_duration Prosa_Behavior_Time_instant
           (instHAdd_inst1 Prosa_Behavior_Time_instant instAddNat)
           (Prosa_Behavior_Job_JobArrival_job_arrival Job1
              inst_4 ja1
              (job1_of j2))
           (arrival_delay j2))
        t))
  (List_flatten Job2
     (List_map Job1 (List Job2) job2_of
        (Prosa_Behavior_Arrival_sequence_arrivals_up_to Job1
           inst_4 arr_seq1 t)))
     : forall (Job1 Job2 : Prosa_Behavior_Job_JobType)
         (inst_4 : 
          DecidableEq Job1),
       DecidableEq Job2 ->
       Prosa_Behavior_Job_JobArrival Job1
         inst_4 ->
       (Job2 -> Job1) ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job1
         inst_4 ->
       (Job1 -> List Job2) ->
       (Job2 -> Prosa_Behavior_Time_duration) -> Prosa_Behavior_Time_instant -> List Job2

Arguments Prosa_Analysis_Definitions_DelayPropagation_propagated_arrival_sequence 
  Job1 Job2 inst_4
  inst_7 
  ja1 job1_of%_function_scope arr_seq1 (job2_of arrival_delay)%_function_scope t
```
