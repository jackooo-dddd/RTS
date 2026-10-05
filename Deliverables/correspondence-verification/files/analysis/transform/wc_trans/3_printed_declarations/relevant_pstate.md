# `relevant_pstate`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.transform.wc_trans.relevant_pstate`
- Lean: `Prosa.Analysis.Transform.WcTrans.relevant_pstate`
- Certificate: `relevant_pstate_correspondence`

## Official Rocq

```coq
relevant_pstate : forall {Job : JobType}, JobArrival Job -> nat -> option (Equality.sort Job) -> bool

relevant_pstate is not universe polymorphic
Arguments relevant_pstate {Job H} reference_time%nat_scope pstate
relevant_pstate is transparent
Expands to: Constant prosa.analysis.transform.wc_trans.relevant_pstate
Declared in library prosa.analysis.transform.wc_trans, line 33, characters 13-28
@relevant_pstate
     : forall Job : JobType, JobArrival Job -> nat -> option (Equality.sort Job) -> bool
```

Body:

```coq
relevant_pstate =
fun (Job : JobType) (H : JobArrival Job) (reference_time : nat) (pstate : option (Equality.sort Job)) =>
match pstate with
| @Some _ j => @job_arrival Job H j <= reference_time
| @None _ => false
end
     : forall {Job : JobType}, JobArrival Job -> nat -> option (Equality.sort Job) -> bool

Arguments relevant_pstate {Job H} reference_time%nat_scope pstate
```

## Lean

```lean
@Prosa.Analysis.Transform.WcTrans.relevant_pstate : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → [Prosa.Behavior.Job.JobArrival Job] → ℕ → Option Job → Bool
```

Body:

```lean
def Prosa.Analysis.Transform.WcTrans.relevant_pstate.{u_1} : {Job : Prosa.Behavior.Job.JobType} →
  [inst : DecidableEq Job] → [Prosa.Behavior.Job.JobArrival Job] → ℕ → Option Job → Bool :=
fun {Job} [DecidableEq Job] [Prosa.Behavior.Job.JobArrival Job] reference_time pstate =>
  match pstate with
  | none => false
  | some j => decide (Prosa.Behavior.Job.job_arrival j ≤ reference_time)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Transform_WcTrans_relevant_pstate
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       Nat -> Option Job -> Bool
```

Body:

```coq
Prosa_Analysis_Transform_WcTrans_relevant_pstate@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Job : Prosa_Behavior_Job_JobType)
  (inst_3 : DecidableEq Job)
  (inst_6 : Prosa_Behavior_Job_JobArrival Job
                                                                            inst_3)
  (reference_time : Nat) (pstate : Option Job) =>
Prosa_Analysis_Transform_WcTrans_relevant_pstate_match_1 Job (fun _ : Option Job => Bool) pstate
  (fun _ : Unit => Bool_false)
  (fun j : Job =>
   Decidable_decide
     (LE_le_inst1 Prosa_Behavior_Time_instant instLENat
        (Prosa_Behavior_Job_JobArrival_job_arrival Job
           inst_3
           inst_6 j)
        reference_time)
     (Nat_decLe
        (Prosa_Behavior_Job_JobArrival_job_arrival Job
           inst_3
           inst_6 j)
        reference_time))
     : forall (Job : Prosa_Behavior_Job_JobType)
         (inst_3 : DecidableEq Job),
       Prosa_Behavior_Job_JobArrival Job inst_3 ->
       Nat -> Option Job -> Bool

Arguments Prosa_Analysis_Transform_WcTrans_relevant_pstate Job
  inst_3
  inst_6 reference_time%_Nat_scope 
  pstate
```
