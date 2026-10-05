# `fp_blackout_bound`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.facts.model.overheads.sbf.fp.fp_blackout_bound`
- Lean: `Prosa.Analysis.Facts.Model.Overheads.Sbf.Fp.fp_blackout_bound`
- Certificate: `fp_blackout_bound_correspondence`

## Official Rocq

```coq
fp_blackout_bound :
forall {Task : TaskType},
FP_policy Task ->
MaxArrivals Task ->
seq (Equality.sort Task) -> duration -> duration -> duration -> Equality.sort Task -> duration -> nat

fp_blackout_bound is not universe polymorphic
Arguments fp_blackout_bound {Task FP H} ts%seq_scope DB CSB CRPDB tsk Δ
fp_blackout_bound is transparent
Expands to: Constant prosa.analysis.facts.model.overheads.sbf.fp.fp_blackout_bound
Declared in library prosa.analysis.facts.model.overheads.sbf.fp, line 40, characters 13-30
@fp_blackout_bound
     : forall Task : TaskType,
       FP_policy Task ->
       MaxArrivals Task ->
       seq (Equality.sort Task) -> duration -> duration -> duration -> Equality.sort Task -> duration -> nat
```

Body:

```coq
fp_blackout_bound =
fun (Task : TaskType) (FP : FP_policy Task) (H : MaxArrivals Task) (ts : seq (Equality.sort Task))
  (DB CSB CRPDB : duration) (tsk : Equality.sort Task) (Δ : duration) =>
(DB + CSB + CRPDB) * (1 + 2 * (\sum_(tsko <- ts | @hep_task Task FP tsko tsk) @max_arrivals Task H tsko Δ))
     : forall {Task : TaskType},
       FP_policy Task ->
       MaxArrivals Task ->
       seq (Equality.sort Task) -> duration -> duration -> duration -> Equality.sort Task -> duration -> nat

Arguments fp_blackout_bound {Task FP H} ts%seq_scope DB CSB CRPDB tsk Δ
```

## Lean

```lean
@Prosa.Analysis.Facts.Model.Overheads.Sbf.Fp.fp_blackout_bound : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [FP : Prosa.Model.Priority.Definitions.FP_policy Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        List Task →
          Prosa.Behavior.Time.duration →
            Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Task → Prosa.Behavior.Time.duration → ℕ
```

Body:

```lean
def Prosa.Analysis.Facts.Model.Overheads.Sbf.Fp.fp_blackout_bound.{u_1} : {Task : Prosa.Model.Task.Concept.TaskType} →
  [inst : DecidableEq Task] →
    [FP : Prosa.Model.Priority.Definitions.FP_policy Task] →
      [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] →
        List Task →
          Prosa.Behavior.Time.duration →
            Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Task → Prosa.Behavior.Time.duration → ℕ :=
fun {Task} [DecidableEq Task] [Prosa.Model.Priority.Definitions.FP_policy Task]
    [Prosa.Model.Task.Arrival.Curves.MaxArrivals Task] ts DB CSB CRPDB tsk Δ =>
  (DB + CSB + CRPDB) *
    (1 +
      2 *
        Prosa.Util.Sum.sumFiltered ts (fun tsko => Prosa.Model.Priority.Definitions.hep_task tsko tsk) fun tsko =>
          Prosa.Model.Task.Arrival.Curves.max_arrivals tsko Δ)
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Overheads_Sbf_Fp_fp_blackout_bound
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task ->
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration -> Task -> Prosa_Behavior_Time_duration -> Nat
```

Body:

```coq
Prosa_Analysis_Facts_Model_Overheads_Sbf_Fp_fp_blackout_bound@{u_1 Lean.u_1+1.0 Lean.u_1+2.0} =
fun (Task : Prosa_Model_Task_Concept_TaskType)
  (inst_3 : DecidableEq Task)
  (FP : Prosa_Model_Priority_Definitions_FP_policy Task
          inst_3)
  (inst_8 : 
   Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
     inst_3)
  (ts : List Task) (DB CSB CRPDB : Prosa_Behavior_Time_duration) (tsk : Task)
  (_UU0394_ : Prosa_Behavior_Time_duration) =>
HMul_hMul_inst7 Prosa_Behavior_Time_duration Nat Prosa_Behavior_Time_duration
  (instHMul_inst1 Prosa_Behavior_Time_duration instMulNat)
  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
     (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
     (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
        (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) DB CSB)
     CRPDB)
  (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))
     (HMul_hMul_inst7 Nat Nat Nat (instHMul_inst1 Nat instMulNat) (OfNat_ofNat_inst1 Nat 2 (instOfNatNat 2))
        (Prosa_Util_Sum_sumFiltered Task ts
           (fun tsko : Task =>
            Prosa_Model_Priority_Definitions_FP_policy_hep_task Task
              inst_3 FP tsko tsk)
           (fun tsko : Task =>
            Prosa_Model_Task_Arrival_Curves_MaxArrivals_max_arrivals Task
              inst_3
              inst_8 tsko _UU0394_))))
     : forall (Task : Prosa_Model_Task_Concept_TaskType)
         (inst_3 : 
          DecidableEq Task),
       Prosa_Model_Priority_Definitions_FP_policy Task
         inst_3 ->
       Prosa_Model_Task_Arrival_Curves_MaxArrivals Task
         inst_3 ->
       List Task ->
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration ->
       Prosa_Behavior_Time_duration -> Task -> Prosa_Behavior_Time_duration -> Nat

Arguments Prosa_Analysis_Facts_Model_Overheads_Sbf_Fp_fp_blackout_bound Task
  inst_3 
  FP inst_8 
  ts DB CSB CRPDB tsk a____at____internal__hyg0
```
