# `refine_cons`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.refinements.refine_cons`
- Lean: `Prosa.Implementation.Refinements.Refinements.refine_cons`
- Certificate: `refine_cons_correspondence`

## Official Rocq

```coq
refine_cons :
forall (A C : Type) (rAC : A -> C -> Type),
@refines (A -> seq A -> seq A) (C -> seq C -> seq C) (rAC ==> @list_R A C rAC ==> @list_R A C rAC) 
  (@cons A) (@cons C)

refine_cons is not universe polymorphic
Arguments refine_cons (A C)%_type_scope rAC%_function_scope
refine_cons is opaque
Expands to: Constant prosa.implementation.refinements.refinements.refine_cons
Declared in library prosa.implementation.refinements.refinements, line 301, characters 16-27
refine_cons
     : forall (A C : Type) (rAC : A -> C -> Type),
       @refines (A -> seq A -> seq A) (C -> seq C -> seq C) (rAC ==> @list_R A C rAC ==> @list_R A C rAC)
         (@cons A) (@cons C)
```

## Lean

```lean
Prosa.Implementation.Refinements.Refinements.refine_cons : (A C : Type) →
  (rAC : A → C → Type) →
    Prosa.Implementation.Refinements.Refinements.refines
      (Prosa.Implementation.Refinements.Refinements.hrespectful rAC
        (Prosa.Implementation.Refinements.Refinements.hrespectful
          (Prosa.Implementation.Refinements.Refinements.list_R rAC)
          (Prosa.Implementation.Refinements.Refinements.list_R rAC)))
      List.cons List.cons
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_refine_cons
     : forall (A C : Type) (rAC : A -> C -> Type),
       Prosa_Implementation_Refinements_Refinements_refines (A -> List_inst1 A -> List_inst1 A)
         (C -> List_inst1 C -> List_inst1 C)
         (Prosa_Implementation_Refinements_Refinements_hrespectful A C (List_inst1 A -> List_inst1 A)
            (List_inst1 C -> List_inst1 C) rAC
            (Prosa_Implementation_Refinements_Refinements_hrespectful (List_inst1 A) 
               (List_inst1 C) (List_inst1 A) (List_inst1 C)
               (Prosa_Implementation_Refinements_Refinements_list_R A C rAC)
               (Prosa_Implementation_Refinements_Refinements_list_R A C rAC)))
         (List_cons_inst1 A) (List_cons_inst1 C)
```
