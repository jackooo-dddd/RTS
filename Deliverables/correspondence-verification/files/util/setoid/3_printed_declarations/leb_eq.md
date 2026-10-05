# `leb_eq`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.setoid.leb_eq`
- Lean: `Prosa.Util.Setoid.leb_eq`
- Certificate: `leb_eq_statement_certificate`

## Official Rocq

```coq
leb_eq : forall a b : bool, leb a b <-> (is_true a -> is_true b)

leb_eq is not universe polymorphic
Arguments leb_eq (a b)%bool_scope
leb_eq is opaque
Expands to: Constant prosa.util.setoid.leb_eq
Declared in library prosa.util.setoid, line 15, characters 6-12
leb_eq
     : forall a b : bool, leb a b <-> (is_true a -> is_true b)
```

## Lean

```lean
Prosa.Util.Setoid.leb_eq : ∀ (a b : Bool), Prosa.Util.Setoid.leb a b ↔ a = true → b = true
```

## Lean, imported into Rocq

```coq
Prosa_Util_Setoid_leb_eq
     : forall a b : Bool, Iff (Prosa_Util_Setoid_leb a b) (@eq Bool a Bool_true -> @eq Bool b Bool_true)
```
