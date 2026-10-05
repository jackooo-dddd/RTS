# `refine_size`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.refinements.refine_size`
- Lean: `Prosa.Implementation.Refinements.Refinements.refine_size`
- Certificate: `refine_size_correspondence`

## Official Rocq

```coq
refine_size :
forall (A C : Type) (rAC : A -> C -> Type),
@refines (seq A -> nat) (seq C -> N) (@list_R A C rAC ==> Rnat) (@size A) (@size_T N zero_N one_N add_N C)

refine_size is not universe polymorphic
Arguments refine_size (A C)%_type_scope rAC%_function_scope
refine_size is opaque
Expands to: Constant prosa.implementation.refinements.refinements.refine_size
Declared in library prosa.implementation.refinements.refinements, line 327, characters 16-27
refine_size
     : forall (A C : Type) (rAC : A -> C -> Type),
       @refines (seq A -> nat) (seq C -> N) (@list_R A C rAC ==> Rnat) (@size A)
         (@size_T N zero_N one_N add_N C)
```

## Lean

```lean
Prosa.Implementation.Refinements.Refinements.refine_size : (A C : Type) →
  (rAC : A → C → Type) →
    Prosa.Implementation.Refinements.Refinements.refines
      (Prosa.Implementation.Refinements.Refinements.hrespectful
        (Prosa.Implementation.Refinements.Refinements.list_R rAC) Prosa.Implementation.Refinements.Refinements.Rnat)
      List.length Prosa.Implementation.Refinements.Refinements.size_T
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_refine_size
     : forall (A C : Type) (rAC : A -> C -> Type),
       Prosa_Implementation_Refinements_Refinements_refines (List_inst1 A -> Nat)
         (List_inst1 C -> Prosa_Implementation_Refinements_Refinements_N)
         (Prosa_Implementation_Refinements_Refinements_hrespectful (List_inst1 A) 
            (List_inst1 C) Nat Prosa_Implementation_Refinements_Refinements_N
            (Prosa_Implementation_Refinements_Refinements_list_R A C rAC)
            Prosa_Implementation_Refinements_Refinements_Rnat)
         (List_length_inst1 A)
         (Prosa_Implementation_Refinements_Refinements_size_T Prosa_Implementation_Refinements_Refinements_N
            Prosa_Implementation_Refinements_Refinements_zero_N
            Prosa_Implementation_Refinements_Refinements_one_N
            Prosa_Implementation_Refinements_Refinements_add_N C)
```
