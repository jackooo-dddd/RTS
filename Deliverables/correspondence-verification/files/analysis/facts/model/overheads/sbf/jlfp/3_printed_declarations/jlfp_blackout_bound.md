# `jlfp_blackout_bound`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.facts.model.overheads.sbf.jlfp.jlfp_blackout_bound`
- Lean: `Prosa.Analysis.Facts.Model.Overheads.Sbf.Jlfp.jlfp_blackout_bound`
- Certificate: `jlfp_blackout_bound_correspondence`

## Official Rocq

```coq
jlfp_blackout_bound :
forall {Task : TaskType},
MaxArrivals Task -> seq (Equality.sort Task) -> duration -> duration -> duration -> duration -> nat

jlfp_blackout_bound is not universe polymorphic
Arguments jlfp_blackout_bound {Task H} ts%seq_scope DB CSB CRPDB Δ
jlfp_blackout_bound is transparent
Expands to: Constant prosa.analysis.facts.model.overheads.sbf.jlfp.jlfp_blackout_bound
Declared in library prosa.analysis.facts.model.overheads.sbf.jlfp, line 35, characters 13-32
@jlfp_blackout_bound
     : forall Task : TaskType,
       MaxArrivals Task -> seq (Equality.sort Task) -> duration -> duration -> duration -> duration -> nat
```

Body:

```coq
jlfp_blackout_bound =
fun (Task : TaskType) (H : MaxArrivals Task) (ts : seq (Equality.sort Task)) (DB CSB CRPDB Δ : duration) =>
(DB + CSB + CRPDB) * (1 + 2 * (\sum_(tsk <- ts) @max_arrivals Task H tsk Δ))
     : forall {Task : TaskType},
       MaxArrivals Task -> seq (Equality.sort Task) -> duration -> duration -> duration -> duration -> nat

Arguments jlfp_blackout_bound {Task H} ts%seq_scope DB CSB CRPDB Δ
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Overheads.Sbf.Jlfp.jlfp_blackout_bound : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
      List Task →
        Prosa.Behavior.Time.duration →
          Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → ℕ
```

Body:

```lean
def Prosa.Analysis.Facts.Model.Overheads.Sbf.Jlfp.jlfp_blackout_bound.{u_1} : {Task :
    Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
      List Task →
        Prosa.Behavior.Time.duration →
          Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] ts DB CSB CRPDB Δ =>
  (DB + CSB + CRPDB) * (1 + 2 * Prosa.Util.Sum.sumSeq ts fun tsk => Prosa.Model.Task.Arrival.Curves.max_arrivals tsk Δ)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Overheads_Sbf_Jlfp_jlfp_blackout_bound
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task ->
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Nat
```

Body:

```coq
Prosa_Analysis_Facts_Model_Overheads_Sbf_Jlfp_jlfp_blackout_bound@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (inst_6 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (ts : List Task) (DB CSB CRPDB _UU0394_ : Prosa_Behavior_Time_duration) =>
HMul_hMul_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
  (instHMul_inst1 Prosa_Behavior_Time_duration instMulNat)
  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
     (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
     (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
        (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) DB CSB)
     CRPDB)
  (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))
     (HMul_hMul_inst7 Nat Nat Nat (instHMul_inst1 Nat instMulNat) (OfNat_ofNat_inst1 Nat 2 (instOfNatNat 2))
        (Prosa_Util_Sum_sumSeq Task ts
           (fun tsk : Task =>
            Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
              inst_3
              inst_6 tsk _UU0394_))))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task ->
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration -> Nat

Arguments Prosa_Analysis_Facts_Model_Overheads_Sbf_Jlfp_jlfp_blackout_bound Task
  inst_3
  inst_6 
  ts DB CSB CRPDB a____at____internal__hyg0
```
