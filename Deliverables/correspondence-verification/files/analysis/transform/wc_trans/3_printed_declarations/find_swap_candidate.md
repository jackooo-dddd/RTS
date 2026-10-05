# `find_swap_candidate`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.transform.wc_trans.find_swap_candidate`
- Lean: `Prosa.Analysis.Transform.WcTrans.find_swap_candidate`
- Certificate: `find_swap_candidate_correspondence`

## Official Rocq

```coq
find_swap_candidate :
forall {Job : JobType},
JobArrival Job ->
JobDeadline Job -> arrival_sequence Job -> (nat -> option (Equality.sort Job)) -> instant -> nat

find_swap_candidate is not universe polymorphic
Arguments find_swap_candidate {Job H H1} arr_seq sched%function_scope t
find_swap_candidate is transparent
Expands to: Constant prosa.analysis.transform.wc_trans.find_swap_candidate
Declared in library prosa.analysis.transform.wc_trans, line 49, characters 13-32
@find_swap_candidate
     : forall Job : JobType,
       JobArrival Job ->
       JobDeadline Job -> arrival_sequence Job -> (nat -> option (Equality.sort Job)) -> instant -> nat
```

Body:

```coq
find_swap_candidate =
fun (Job : JobType) (H : JobArrival Job) (H1 : JobDeadline Job) (arr_seq : arrival_sequence Job)
  (sched : nat -> option (Equality.sort Job)) (t : instant) =>
let order := fun=> xpred0 in
let max_dl := @max_deadline_for_jobs_arrived_before Job H1 arr_seq t in
let search_result := @search_arg (option (Equality.sort Job)) sched (@relevant_pstate Job H t) order t max_dl
  in
match search_result with
| @Some _ t_swap => t_swap
| @None _ => t
end
     : forall {Job : JobType},
       JobArrival Job ->
       JobDeadline Job -> arrival_sequence Job -> (nat -> option (Equality.sort Job)) -> instant -> nat

Arguments find_swap_candidate {Job H H1} arr_seq sched%function_scope t
```

## Lean

```lean
@Prosa.Analysis.Transform.WcTrans.find_swap_candidate : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] →
      [Prosa.Behavior.Job.JobDeadline Job] →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job → (ℕ → Option Job) → Prosa.Behavior.Time.instant → ℕ
```

Body:

```lean
def Prosa.Analysis.Transform.WcTrans.find_swap_candidate.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] →
    [Prosa.Behavior.Job.JobArrival Job] →
      [Prosa.Behavior.Job.JobDeadline Job] →
        Prosa.Behavior.Arrival_sequence.arrival_sequence Job → (ℕ → Option Job) → Prosa.Behavior.Time.instant → ℕ :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] [Prosa.Behavior.Job.JobDeadline Job] arr_seq sched t =>
  have order := fun x x_1 => false;
  have max_dl := Prosa.Analysis.Transform.WcTrans.max_deadline_for_jobs_arrived_before arr_seq t;
  have search_result :=
    Prosa.Util.SearchArg.search_arg sched (Prosa.Analysis.Transform.WcTrans.relevant_pstate t) order t max_dl;
  match search_result with
  | some t_swap => t_swap
  | none => t
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Transform_WcTrans_find_swap_candidate
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Job_JobDeadline Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       (Nat -> Option Job) -> Prosa_Behavior_Time_instant -> Nat
```

Body:

```coq
Prosa_Analysis_Transform_WcTrans_find_swap_candidate@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobArrival Job
                                                                             inst_3)
  (inst_9 : Prosa_Behavior_Job_JobDeadline Job
                                                                             inst_3)
  (arr_seq : Prosa_Behavior_Arrival_sequence_arrival_sequence Job
               inst_3)
  (sched : Nat -> Option Job) (t : Prosa_Behavior_Time_instant) =>
let order := fun _ _ : Option Job => Bool_false in
let max_dl :=
  Prosa_Analysis_Transform_WcTrans_max_deadline_for_jobs_arrived_before Job
    inst_3
    inst_9 arr_seq t
  in
let search_result :=
  Prosa_Util_SearchArg_search_arg (Option Job) sched
    (Prosa_Analysis_Transform_WcTrans_relevant_pstate Job
       inst_3
       inst_6 t)
    order t max_dl
  in
Prosa_Analysis_Transform_WcTrans_find_swap_candidate_match_1 (fun _ : Option_inst1 Nat => Nat) search_result
  (fun acc : Nat => acc) (fun _ : Unit => t)
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job
         inst_3 ->
       Prosa_Behavior_Job_JobDeadline Job
         inst_3 ->
       Prosa_Behavior_Arrival_sequence_arrival_sequence Job
         inst_3 ->
       (Nat -> Option Job) -> Prosa_Behavior_Time_instant -> Nat

Arguments Prosa_Analysis_Transform_WcTrans_find_swap_candidate Job
  inst_3
  inst_6
  inst_9 arr_seq sched%_function_scope
  arrived_before
```
