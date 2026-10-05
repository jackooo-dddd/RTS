# `refine_flatten`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.refinements.refine_flatten`
- Lean: `Prosa.Implementation.Refinements.Refinements.refine_flatten`
- Certificate: `refine_flatten_correspondence`

## Official Rocq

```coq
refine_flatten :
forall {A A' : Type} (rA : A -> A' -> Type),
@refines (seq (seq A) -> seq A) (seq (seq A') -> seq A')
  (@list_R (seq A) (seq A') (@list_R A A' rA) ==> @list_R A A' rA) (@flatten A) (@flatten A')

refine_flatten is not universe polymorphic
Arguments refine_flatten {A A'}%_type_scope rA%_function_scope
refine_flatten is opaque
Expands to: Constant prosa.implementation.refinements.refinements.refine_flatten
Declared in library prosa.implementation.refinements.refinements, line 293, characters 16-30
@refine_flatten
     : forall (A A' : Type) (rA : A -> A' -> Type),
       @refines (seq (seq A) -> seq A) (seq (seq A') -> seq A')
         (@list_R (seq A) (seq A') (@list_R A A' rA) ==> @list_R A A' rA) (@flatten A) 
         (@flatten A')
```

## Lean

```lean
@Prosa.Implementation.Refinements.Refinements.refine_flatten : {A A' : Type} →
  (rA : A → A' → Type) →
    Prosa.Implementation.Refinements.Refinements.refines
      (Prosa.Implementation.Refinements.Refinements.hrespectful
        (Prosa.Implementation.Refinements.Refinements.list_R (Prosa.Implementation.Refinements.Refinements.list_R rA))
        (Prosa.Implementation.Refinements.Refinements.list_R rA))
      List.flatten List.flatten
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_refine_flatten
     : forall (A A' : Type) (rA : A -> A' -> Type),
       Prosa_Implementation_Refinements_Refinements_refines (List_inst1 (List_inst1 A) -> List_inst1 A)
         (List_inst1 (List_inst1 A') -> List_inst1 A')
         (Prosa_Implementation_Refinements_Refinements_hrespectful (List_inst1 (List_inst1 A))
            (List_inst1 (List_inst1 A')) (List_inst1 A) (List_inst1 A')
            (Prosa_Implementation_Refinements_Refinements_list_R (List_inst1 A) (List_inst1 A')
               (Prosa_Implementation_Refinements_Refinements_list_R A A' rA))
            (Prosa_Implementation_Refinements_Refinements_list_R A A' rA))
         (List_flatten_inst1 A) (List_flatten_inst1 A')
```
