# `modusponens`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.tactics.modusponens`
- Lean: `Prosa.Util.Tactics.modusponens`
- Certificate: `modusponens_statement_certificate`

## Official Rocq

```coq
modusponens : forall P Q : Prop, P -> (P -> Q) -> Q

modusponens is not universe polymorphic
Arguments modusponens (P Q)%type_scope _ _%function_scope
modusponens is opaque
Expands to: Constant prosa.util.tactics.modusponens
Declared in library prosa.util.tactics, line 14, characters 6-17
modusponens
     : forall P Q : Prop, P -> (P -> Q) -> Q
```

## Lean

```lean
Prosa.Util.Tactics.modusponens : ∀ (P Q : Prop), P → (P → Q) → Q
```

## Lean, imported into Rocq

```coq
Prosa_Util_Tactics_modusponens
     : forall P Q : SProp, P -> (P -> Q) -> Q
```
