# `refine_foldr_max`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.refinements.refinements.refine_foldr_max`
- Lean: `Prosa.Implementation.Refinements.Refinements.refine_foldr_max`
- Certificate: `refine_foldr_max_correspondence`

## Official Rocq

```coq
refine_foldr_max :
forall {T1 T2 : Type} (xs : seq T1) (xs' : seq T2) (R : T1 -> bool) (R' : T2 -> bool) 
  (F : T1 -> nat) (F' : T2 -> N) (rT : T1 -> T2 -> Type),
@refines (seq T1) (seq T2) (@list_R T1 T2 rT) xs xs' ->
@refines (T1 -> nat) (T2 -> N) (rT ==> Rnat) F F' ->
@refines (T1 -> bool) (T2 -> bool) (rT ==> bool_R) R R' ->
@refines nat N Rnat (\max_(x <- xs | R x) F x)
  (@foldr N N (@maxn_T N lt_N) 0%C [seq F' x' | x' <- xs' & R' x'])

refine_foldr_max is not universe polymorphic
Arguments refine_foldr_max {T1 T2}%_type_scope (xs xs')%_seq_scope (R R' F F' rT)%_function_scope _ _ _
refine_foldr_max is opaque
Expands to: Constant prosa.implementation.refinements.refinements.refine_foldr_max
Declared in library prosa.implementation.refinements.refinements, line 463, characters 8-24
@refine_foldr_max
     : forall (T1 T2 : Type) (xs : seq T1) (xs' : seq T2) (R : T1 -> bool) (R' : T2 -> bool) 
         (F : T1 -> nat) (F' : T2 -> N) (rT : T1 -> T2 -> Type),
       @refines (seq T1) (seq T2) (@list_R T1 T2 rT) xs xs' ->
       @refines (T1 -> nat) (T2 -> N) (rT ==> Rnat) F F' ->
       @refines (T1 -> bool) (T2 -> bool) (rT ==> bool_R) R R' ->
       @refines nat N Rnat (\max_(x <- xs | R x) F x)
         (@foldr N N (@maxn_T N lt_N) 0%C [seq F' x' | x' <- xs' & R' x'])
```

## Lean

```lean
@Prosa.Implementation.Refinements.Refinements.refine_foldr_max : {T1 T2 : Type} →
  (xs : List T1) →
    (xs' : List T2) →
      (R : T1 → Bool) →
        (R' : T2 → Bool) →
          (F : T1 → ℕ) →
            (F' : T2 → Prosa.Implementation.Refinements.Refinements.N) →
              (rT : T1 → T2 → Type) →
                Prosa.Implementation.Refinements.Refinements.refines
                    (Prosa.Implementation.Refinements.Refinements.list_R rT) xs xs' →
                  Prosa.Implementation.Refinements.Refinements.refines
                      (Prosa.Implementation.Refinements.Refinements.hrespectful rT
                        Prosa.Implementation.Refinements.Refinements.Rnat)
                      F F' →
                    Prosa.Implementation.Refinements.Refinements.refines
                        (Prosa.Implementation.Refinements.Refinements.hrespectful rT
                          Prosa.Implementation.Refinements.Refinements.bool_R)
                        R R' →
                      Prosa.Implementation.Refinements.Refinements.refines
                        Prosa.Implementation.Refinements.Refinements.Rnat (Prosa.Util.Sum.maxFiltered xs R F)
                        (List.foldr Prosa.Implementation.Refinements.Refinements.maxn_T
                          Prosa.Implementation.Refinements.Refinements.zero_op (List.map F' (List.filter R' xs')))
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_refine_foldr_max
     : forall (T1 T2 : Type) (xs : List_inst1 T1) (xs' : List_inst1 T2) (R : T1 -> Bool) 
         (R' : T2 -> Bool) (F : T1 -> Nat) (F' : T2 -> Prosa_Implementation_Refinements_Refinements_N)
         (rT : T1 -> T2 -> Type),
       Prosa_Implementation_Refinements_Refinements_refines (List_inst1 T1) (List_inst1 T2)
         (Prosa_Implementation_Refinements_Refinements_list_R T1 T2 rT) xs xs' ->
       Prosa_Implementation_Refinements_Refinements_refines (T1 -> Nat)
         (T2 -> Prosa_Implementation_Refinements_Refinements_N)
         (Prosa_Implementation_Refinements_Refinements_hrespectful T1 T2 Nat
            Prosa_Implementation_Refinements_Refinements_N rT
            Prosa_Implementation_Refinements_Refinements_Rnat)
         F F' ->
       Prosa_Implementation_Refinements_Refinements_refines (T1 -> Bool) (T2 -> Bool)
         (Prosa_Implementation_Refinements_Refinements_hrespectful T1 T2 Bool Bool rT
            Prosa_Implementation_Refinements_Refinements_bool_R)
         R R' ->
       Prosa_Implementation_Refinements_Refinements_refines Nat
         Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_Rnat
         (Prosa_Util_Sum_maxFiltered_inst1 T1 xs R F)
         (List_foldr_inst3 Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_N
            (Prosa_Implementation_Refinements_Refinements_maxn_T
               Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_lt_N)
            (Prosa_Implementation_Refinements_Refinements_zero_of_zero_op
               Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_zero_N)
            (List_map_inst3 T2 Prosa_Implementation_Refinements_Refinements_N F'
               (List_filter_inst1 T2 R' xs')))
```
