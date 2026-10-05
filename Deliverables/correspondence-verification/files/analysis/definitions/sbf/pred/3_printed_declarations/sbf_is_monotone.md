# `sbf_is_monotone`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.definitions.sbf.pred.sbf_is_monotone`
- Lean: `Prosa.Analysis.Definitions.Sbf.Pred.sbf_is_monotone`
- Certificate: `pred_sbf_is_monotone_correspondence`

## Official Rocq

```coq
sbf_is_monotone : (duration -> work) -> Prop

sbf_is_monotone is not universe polymorphic
Arguments sbf_is_monotone SBF%function_scope
sbf_is_monotone is transparent
Expands to: Constant prosa.analysis.definitions.sbf.pred.sbf_is_monotone
Declared in library prosa.analysis.definitions.sbf.pred, line 53, characters 13-28
sbf_is_monotone
     : (duration -> work) -> Prop
```

Body:

```coq
sbf_is_monotone = [eta @monotone nat leq]
     : (duration -> work) -> Prop

Arguments sbf_is_monotone SBF%function_scope
```

## Lean

```lean
Prosa.Analysis.Definitions.Sbf.Pred.sbf_is_monotone : (Prosa.Behavior.Time.duration → Prosa.Behavior.Job.work) → Prop
```

Body:

```lean
def Prosa.Analysis.Definitions.Sbf.Pred.sbf_is_monotone : (Prosa.Behavior.Time.duration → Prosa.Behavior.Job.work) →
  Prop :=
fun SBF => Prosa.Util.Rel.monotone (fun x y => decide (x ≤ y)) SBF
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Definitions_Sbf_Pred_sbf_is_monotone
     : (Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) -> SProp
```

Body:

```coq
Prosa_Analysis_Definitions_Sbf_Pred_sbf_is_monotone@{} =
fun SBF : Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work =>
Prosa_Util_Rel_monotone_inst1 Prosa_Behavior_Time_duration
  (fun x y : Prosa_Behavior_Time_duration =>
   Decidable_decide (LE_le_inst1 Prosa_Behavior_Time_duration instLENat x y) (Nat_decLe x y))
  SBF
     : (Prosa_Behavior_Time_duration -> Prosa_Behavior_Job_work) -> SProp

Arguments Prosa_Analysis_Definitions_Sbf_Pred_sbf_is_monotone SBF%_function_scope
```
