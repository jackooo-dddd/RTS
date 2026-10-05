# `refine_nil`

- Kind (Rocq): Instance
- Rocq: `prosa.implementation.refinements.refinements.refine_nil`
- Lean: `Prosa.Implementation.Refinements.Refinements.refine_nil`
- Certificate: `refine_nil_correspondence`

## Official Rocq

```coq
refine_nil : forall (A C : Type) (rAC : A -> C -> Type), @refines (seq A) (seq C) (@list_R A C rAC) [::] [::]

refine_nil is not universe polymorphic
Arguments refine_nil (A C)%_type_scope rAC%_function_scope
refine_nil is opaque
Expands to: Constant prosa.implementation.refinements.refinements.refine_nil
Declared in library prosa.implementation.refinements.refinements, line 308, characters 16-26
refine_nil
     : forall (A C : Type) (rAC : A -> C -> Type), @refines (seq A) (seq C) (@list_R A C rAC) [::] [::]
```

## Lean

```lean
Prosa.Implementation.Refinements.Refinements.refine_nil : (A C : Type) →
  (rAC : A → C → Type) →
    Prosa.Implementation.Refinements.Refinements.refines (Prosa.Implementation.Refinements.Refinements.list_R rAC) [] []
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_Refinements_refine_nil
     : forall (A C : Type) (rAC : A -> C -> Type),
       Prosa_Implementation_Refinements_Refinements_refines (List_inst1 A) (List_inst1 C)
         (Prosa_Implementation_Refinements_Refinements_list_R A C rAC) (List_nil_inst1 A) 
         (List_nil_inst1 C)
```
