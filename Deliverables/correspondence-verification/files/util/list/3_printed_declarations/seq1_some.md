# `seq1_some`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.seq1_some`
- Lean: `Prosa.Util.List.seq1_some`
- Certificate: `seq1_some_statement_certificate`

## Official Rocq

```coq
seq1_some :
forall {T : eqType} (x y : Equality.sort T),
([:: x] == [:: y]) = (@Some (Equality.sort T) x == @Some (Equality.sort T) y)

seq1_some is not universe polymorphic
Arguments seq1_some {T} x y
seq1_some is opaque
Expands to: Constant prosa.util.list.seq1_some
Declared in library prosa.util.list, line 306, characters 6-15
@seq1_some
     : forall (T : eqType) (x y : Equality.sort T),
       ([:: x] == [:: y]) = (@Some (Equality.sort T) x == @Some (Equality.sort T) y)
```

## Lean

```lean
@Prosa.Util.List.seq1_some : ∀ {T : Type u_1} [inst : DecidableEq T] (x y : T),
  decide ([x] = [y]) = decide (some x = some y)
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_seq1_some
     : forall (T : Type) (inst_3 : DecidableEq T) (x y : T),
       @eq Bool
         (Decidable_decide (@eq (List T) (List_cons T x (List_nil T)) (List_cons T y (List_nil T)))
            (instDecidableEqList T inst_3
               (List_cons T x (List_nil T)) (List_cons T y (List_nil T))))
         (Decidable_decide (@eq (Option T) (Option_some T x) (Option_some T y))
            (Option_instDecidableEq T inst_3 
               (Option_some T x) (Option_some T y)))
```
