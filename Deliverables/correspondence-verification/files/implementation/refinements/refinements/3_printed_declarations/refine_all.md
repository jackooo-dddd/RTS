# `refine_all`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.refinements.refine_all`
- Lean: `Prosa.Implementation.Refinements.Refinements.refine_all`
- Certificate: `refine_all_correspondence`

## Official Rocq

```coq
refine_all :
forall {A A' : Type} (rA : A -> A' -> Type),
@refines ((A -> bool) -> seq A -> bool) ((A' -> bool) -> seq A' -> bool)
  ((rA ==> bool_R) ==> @list_R A A' rA ==> bool_R) (@all A) (@all A')

refine_all is not universe polymorphic
Arguments refine_all {A A'}%_type_scope rA%_function_scope
refine_all is opaque
Expands to: Constant prosa.implementation.refinements.refinements.refine_all
Declared in library prosa.implementation.refinements.refinements, line 282, characters 16-26
@refine_all
     : forall (A A' : Type) (rA : A -> A' -> Type),
       @refines ((A -> bool) -> seq A -> bool) ((A' -> bool) -> seq A' -> bool)
         ((rA ==> bool_R) ==> @list_R A A' rA ==> bool_R) (@all A) (@all A')
```

## Lean

```lean
@Prosa.Implementation.Refinements.Refinements.refine_all : {A A' : Type} →
  (rA : A → A' → Type) →
    Prosa.Implementation.Refinements.Refinements.refines
      (Prosa.Implementation.Refinements.Refinements.hrespectful
        (Prosa.Implementation.Refinements.Refinements.hrespectful rA
          Prosa.Implementation.Refinements.Refinements.bool_R)
        (Prosa.Implementation.Refinements.Refinements.hrespectful
          (Prosa.Implementation.Refinements.Refinements.list_R rA) Prosa.Implementation.Refinements.Refinements.bool_R))
      (fun P s => s.all P) fun P s => s.all P
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_refine_all
     : forall (A A' : Type) (rA : A -> A' -> Type),
       Prosa_Implementation_Refinements_Refinements_refines ((A -> Bool) -> List_inst1 A -> Bool)
         ((A' -> Bool) -> List_inst1 A' -> Bool)
         (Prosa_Implementation_Refinements_Refinements_hrespectful (A -> Bool) (A' -> Bool)
            (List_inst1 A -> Bool) (List_inst1 A' -> Bool)
            (Prosa_Implementation_Refinements_Refinements_hrespectful A A' Bool Bool rA
               Prosa_Implementation_Refinements_Refinements_bool_R)
            (Prosa_Implementation_Refinements_Refinements_hrespectful (List_inst1 A) 
               (List_inst1 A') Bool Bool (Prosa_Implementation_Refinements_Refinements_list_R A A' rA)
               Prosa_Implementation_Refinements_Refinements_bool_R))
         (fun (P : A -> Bool) (s : List_inst1 A) => List_all_inst1 A s P)
         (fun (P : A' -> Bool) (s : List_inst1 A') => List_all_inst1 A' s P)
```
