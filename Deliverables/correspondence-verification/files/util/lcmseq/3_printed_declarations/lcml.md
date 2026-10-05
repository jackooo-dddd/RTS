# `lcml`

- Kind (Rocq): Definition
- Rocq: `prosa.util.lcmseq.lcml`
- Lean: `Prosa.Util.Lcmseq.lcml`
- Certificate: `lcml_correspondence`

## Official Rocq

```coq
lcml : seq nat -> nat

lcml is not universe polymorphic
Arguments lcml xs%seq_scope
lcml is transparent
Expands to: Constant prosa.util.lcmseq.lcml
Declared in library prosa.util.lcmseq, line 6, characters 11-15
lcml
     : seq nat -> nat
```

Body:

```coq
lcml = [eta @foldr nat nat lcmn 1]
     : seq nat -> nat

Arguments lcml xs%seq_scope
```

## Lean

```lean
Prosa.Util.Lcmseq.lcml : List ℕ → ℕ
```

Body:

```lean
def Prosa.Util.Lcmseq.lcml : List ℕ → ℕ :=
fun xs => List.foldr Nat.lcm 1 xs
```

## Lean, imported into Rocq

```coq
Prosa_Util_Lcmseq_lcml
     : List_inst1 Nat -> Nat
```

Body:

```coq
Prosa_Util_Lcmseq_lcml@{} =
fun xs : List_inst1 Nat => List_foldr_inst3 Nat Nat Nat_lcm (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)) xs
     : List_inst1 Nat -> Nat

Arguments Prosa_Util_Lcmseq_lcml xs
```
