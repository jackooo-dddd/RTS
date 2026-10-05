# `solution_for_A_exists`

- Kind (Rocq): Lemma
- Rocq: `prosa.analysis.abstract.search_space.solution_for_A_exists`
- Lean: `Prosa.Analysis.Abstract.SearchSpace.solution_for_A_exists`
- Certificate: `ss_solution_statement_correspondence`

## Official Rocq

```coq
solution_for_A_exists :
forall (B : time.duration) (interference_bound_function : time.duration -> time.duration -> time.duration)
  (A_sp F_sp : time.duration),
is_true (A_sp + F_sp < B) ->
is_true (interference_bound_function A_sp (A_sp + F_sp) <= A_sp + F_sp) ->
forall A : time.duration,
is_true (A_sp <= A <= A_sp + F_sp) ->
@are_equivalent_at_values_less_than Datatypes_nat__canonical__eqtype_Equality (interference_bound_function A)
  (interference_bound_function A_sp) B ->
exists F : nat,
  A_sp + F_sp = A + F /\ is_true (F <= F_sp) /\ is_true (interference_bound_function A (A + F) <= A + F)

solution_for_A_exists is not universe polymorphic
Arguments solution_for_A_exists B interference_bound_function%function_scope A_sp 
  F_sp H_less_than H_fixpoint A H_bounds_for_A H_equivalent
solution_for_A_exists is opaque
Expands to: Constant prosa.analysis.abstract.search_space.solution_for_A_exists
Declared in library prosa.analysis.abstract.search_space, line 148, characters 10-31
solution_for_A_exists
     : forall (B : time.duration)
         (interference_bound_function : time.duration -> time.duration -> time.duration)
         (A_sp F_sp : time.duration),
       is_true (A_sp + F_sp < B) ->
       is_true (interference_bound_function A_sp (A_sp + F_sp) <= A_sp + F_sp) ->
       forall A : time.duration,
       is_true (A_sp <= A <= A_sp + F_sp) ->
       @are_equivalent_at_values_less_than Datatypes_nat__canonical__eqtype_Equality
         (interference_bound_function A) (interference_bound_function A_sp) B ->
       exists F : nat,
         A_sp + F_sp = A + F /\
         is_true (F <= F_sp) /\ is_true (interference_bound_function A (A + F) <= A + F)
```

## Lean

```lean
Prosa.Analysis.Abstract.SearchSpace.solution_for_A_exists : ∀ (B : Prosa.Behavior.Time.duration)
  (interference_bound_function :
    Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration → Prosa.Behavior.Time.duration)
  (A_sp F_sp : Prosa.Behavior.Time.duration),
  A_sp + F_sp < B →
    interference_bound_function A_sp (A_sp + F_sp) ≤ A_sp + F_sp →
      ∀ (A : Prosa.Behavior.Time.duration),
        A_sp ≤ A ∧ A ≤ A_sp + F_sp →
          Prosa.Analysis.Abstract.SearchSpace.are_equivalent_at_values_less_than (interference_bound_function A)
              (interference_bound_function A_sp) B →
            ∃ F, A_sp + F_sp = A + F ∧ F ≤ F_sp ∧ interference_bound_function A (A + F) ≤ A + F
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Abstract_SearchSpace_solution_for_A_exists
     : forall (B : Prosa_Behavior_Time_duration)
         (interference_bound_function : Prosa_Behavior_Time_duration ->
                                        Prosa_Behavior_Time_duration -> Prosa_Behavior_Time_duration)
         (A_sp F_sp : Prosa_Behavior_Time_duration),
       LT_lt_inst1 Prosa_Behavior_Time_duration instLTNat
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A_sp F_sp)
         B ->
       LE_le_inst1 Prosa_Behavior_Time_duration instLENat
         (interference_bound_function A_sp
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A_sp
               F_sp))
         (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
            Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A_sp F_sp) ->
       forall A : Prosa_Behavior_Time_duration,
       And (LE_le_inst1 Prosa_Behavior_Time_duration instLENat A_sp A)
         (LE_le_inst1 Prosa_Behavior_Time_duration instLENat A
            (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
               Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A_sp
               F_sp)) ->
       Prosa_Analysis_Abstract_SearchSpace_are_equivalent_at_values_less_than_inst1
         Prosa_Behavior_Time_duration instDecidableEqNat (interference_bound_function A)
         (interference_bound_function A_sp) B ->
       Exists Prosa_Behavior_Time_duration
         (fun F : Prosa_Behavior_Time_duration =>
          And
            (@eq Prosa_Behavior_Time_duration
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A_sp
                  F_sp)
               (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                  Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A F))
            (And (LE_le_inst1 Prosa_Behavior_Time_duration instLENat F F_sp)
               (LE_le_inst1 Prosa_Behavior_Time_duration instLENat
                  (interference_bound_function A
                     (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                        Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat)
                        A F))
                  (HAdd_hAdd_inst7 Prosa_Behavior_Time_duration Prosa_Behavior_Time_duration
                     Prosa_Behavior_Time_duration (instHAdd_inst1 Prosa_Behavior_Time_duration instAddNat) A
                     F))))
```
