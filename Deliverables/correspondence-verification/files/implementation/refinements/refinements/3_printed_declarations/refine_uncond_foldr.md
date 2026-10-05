# `refine_uncond_foldr`

- Kind (Rocq): Lemma
- Rocq: `prosa.implementation.refinements.refinements.refine_uncond_foldr`
- Lean: `Prosa.Implementation.Refinements.Refinements.refine_uncond_foldr`
- Certificate: `refine_uncond_foldr_correspondence`

## Official Rocq

```coq
refine_uncond_foldr :
forall {T1 T2 : Type} (xs : seq T1) (xs' : seq T2) (F : T1 -> nat) (F' : T2 -> N) (rT : T1 -> T2 -> Type),
@refines (seq T1) (seq T2) (@list_R T1 T2 rT) xs xs' ->
@refines (T1 -> nat) (T2 -> N) (rT ==> Rnat) F F' ->
@refines nat N Rnat (\sum_(x <- xs) F x) (@foldr N N +%C 0%C [seq F' x' | x' <- xs'])

refine_uncond_foldr is not universe polymorphic
Arguments refine_uncond_foldr {T1 T2}%_type_scope (xs xs')%_seq_scope (F F' rT)%_function_scope _ _
refine_uncond_foldr is opaque
Expands to: Constant prosa.implementation.refinements.refinements.refine_uncond_foldr
Declared in library prosa.implementation.refinements.refinements, line 448, characters 8-27
@refine_uncond_foldr
     : forall (T1 T2 : Type) (xs : seq T1) (xs' : seq T2) (F : T1 -> nat) (F' : T2 -> N)
         (rT : T1 -> T2 -> Type),
       @refines (seq T1) (seq T2) (@list_R T1 T2 rT) xs xs' ->
       @refines (T1 -> nat) (T2 -> N) (rT ==> Rnat) F F' ->
       @refines nat N Rnat (\sum_(x <- xs) F x) (@foldr N N +%C 0%C [seq F' x' | x' <- xs'])
```

## Lean

```lean
@Prosa.Implementation.Refinements.Refinements.refine_uncond_foldr : {T1 T2 : Type} →
  (xs : List T1) →
    (xs' : List T2) →
      (F : T1 → ℕ) →
        (F' : T2 → Prosa.Implementation.Refinements.Refinements.N) →
          (rT : T1 → T2 → Type) →
            Prosa.Implementation.Refinements.Refinements.refines
                (Prosa.Implementation.Refinements.Refinements.list_R rT) xs xs' →
              Prosa.Implementation.Refinements.Refinements.refines
                  (Prosa.Implementation.Refinements.Refinements.hrespectful rT
                    Prosa.Implementation.Refinements.Refinements.Rnat)
                  F F' →
                Prosa.Implementation.Refinements.Refinements.refines Prosa.Implementation.Refinements.Refinements.Rnat
                  (Prosa.Util.Sum.sumSeq xs F)
                  (List.foldr Prosa.Implementation.Refinements.Refinements.add_op
                    Prosa.Implementation.Refinements.Refinements.zero_op (List.map F' xs'))
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_refine_uncond_foldr
     : forall (T1 T2 : Type) (xs : List_inst1 T1) (xs' : List_inst1 T2) (F : T1 -> Nat)
         (F' : T2 -> Prosa_Implementation_Refinements_Refinements_N) (rT : T1 -> T2 -> Type),
       Prosa_Implementation_Refinements_Refinements_refines (List_inst1 T1) (List_inst1 T2)
         (Prosa_Implementation_Refinements_Refinements_list_R T1 T2 rT) xs xs' ->
       Prosa_Implementation_Refinements_Refinements_refines (T1 -> Nat)
         (T2 -> Prosa_Implementation_Refinements_Refinements_N)
         (Prosa_Implementation_Refinements_Refinements_hrespectful T1 T2 Nat
            Prosa_Implementation_Refinements_Refinements_N rT
            Prosa_Implementation_Refinements_Refinements_Rnat)
         F F' ->
       Prosa_Implementation_Refinements_Refinements_refines Nat
         Prosa_Implementation_Refinements_Refinements_N Prosa_Implementation_Refinements_Refinements_Rnat
         (Prosa_Util_Sum_sumSeq_inst1 T1 xs F)
         (List_foldr_inst3 Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_N
            (Prosa_Implementation_Refinements_Refinements_add_of_add_op
               Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_add_N)
            (Prosa_Implementation_Refinements_Refinements_zero_of_zero_op
               Prosa_Implementation_Refinements_Refinements_N
               Prosa_Implementation_Refinements_Refinements_zero_N)
            (List_map_inst3 T2 Prosa_Implementation_Refinements_Refinements_N F' xs'))
```
