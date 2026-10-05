# `size_big_nat`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.bigcat.size_big_nat`
- Lean: `Prosa.Util.Bigcat.size_big_nat`
- Certificate: `size_big_nat_statement_certificate`

## Official Rocq

```coq
size_big_nat :
forall {X : Type} (F : nat -> seq X) (t1 t2 : nat),
@bigop.bigop.body nat nat 0 (bigop.index_iota t1 t2)
  (fun t : nat => @bigop.BigBody nat nat t addn true (@size X (F t))) =
@size X (\cat_(t1<=t<t2)F t)

size_big_nat is not universe polymorphic
Arguments size_big_nat {X}%type_scope F%function_scope (t1 t2)%nat_scope
size_big_nat is opaque
Expands to: Constant prosa.util.bigcat.size_big_nat
Declared in library prosa.util.bigcat, line 125, characters 8-20
@size_big_nat
     : forall (X : Type) (F : nat -> seq X) (t1 t2 : nat),
       @bigop.bigop.body nat nat 0 (bigop.index_iota t1 t2)
         (fun t : nat => @bigop.BigBody nat nat t addn true (@size X (F t))) =
       @size X (\cat_(t1<=t<t2)F t)
```

## Lean

```lean
@Prosa.Util.Bigcat.size_big_nat : ∀ {X : Type u_1} (F : ℕ → List X) (t₁ t₂ : ℕ),
  ∑ t ∈ Finset.Ico t₁ t₂, (F t).length = (Prosa.Util.Notation.bigCat t₁ t₂ F).length
```

## Lean, imported into Rocq

```coq
Prosa_Util_Bigcat_size_big_nat
     : forall (X : Type) (F : Nat -> List X) (t_UU2081_ t_UU2082_ : Nat),
       @eq Nat
         (List_foldr_inst3 Nat Nat Nat_add 0
            (List_map_inst3 Nat Nat (fun t : Nat => List_length X (F t))
               (List_range' t_UU2081_ (Nat_sub t_UU2082_ t_UU2081_) 1)))
         (List_length X
            (List_flatten X
               (List_map_inst1 Nat (List X) (fun i : Nat => F (Nat_add t_UU2081_ i))
                  (List_range_loop (Nat_sub t_UU2082_ t_UU2081_) (List_nil_inst1 Nat)))))
```
