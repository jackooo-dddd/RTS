# `filter_size_rem`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.filter_size_rem`
- Lean: `Prosa.Util.List.filter_size_rem`
- Certificate: `filter_size_rem_statement_certificate`

## Official Rocq

```coq
filter_size_rem :
forall {X : eqType} (x : Equality.sort X) (xs : seq (Equality.sort X)) (P : pred (Equality.sort X)),
is_true (x \in xs) ->
is_true (P x) ->
@size (Equality.sort X) [seq y <- xs | P y] = @size (Equality.sort X) [seq y <- @rem X x xs | P y] + 1

filter_size_rem is not universe polymorphic
Arguments filter_size_rem {X} x xs%seq_scope P _ _
filter_size_rem is opaque
Expands to: Constant prosa.util.list.filter_size_rem
Declared in library prosa.util.list, line 262, characters 6-21
@filter_size_rem
     : forall (X : eqType) (x : Equality.sort X) (xs : seq (Equality.sort X)) (P : pred (Equality.sort X)),
       is_true (x \in xs) ->
       is_true (P x) ->
       @size (Equality.sort X) [seq y <- xs | P y] = @size (Equality.sort X) [seq y <- @rem X x xs | P y] + 1
```

## Lean

```lean
@Prosa.Util.List.filter_size_rem : ∀ {T : Type u_1} [inst : DecidableEq T] (x : T) (xs : List T) (P : T → Bool),
  x ∈ xs → P x = true → (List.filter P xs).length = (List.filter P (xs.erase x)).length + 1
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_filter_size_rem
     : forall (T : Type) (inst_3 : DecidableEq T) 
         (x : T) (xs : List T) (P : T -> Bool),
       Membership_mem T (List T) (List_instMembership T) xs x ->
       @eq Bool (P x) Bool_true ->
       @eq Nat (List_length T (List_filter T P xs))
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat)
            (List_length T
               (List_filter T P
                  (List_erase T (instBEqOfDecidableEq T inst_3)
                     xs x)))
            (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1)))
```
