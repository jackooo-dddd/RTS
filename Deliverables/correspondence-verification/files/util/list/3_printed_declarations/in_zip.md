# `in_zip`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.in_zip`
- Lean: `Prosa.Util.List.in_zip`
- Certificate: `in_zip_statement_certificate`

## Official Rocq

```coq
in_zip :
forall {X Y : eqType} (xs : seq (Equality.sort X)) (ys : seq (Equality.sort Y)) (x x__d : Equality.sort X)
  (y y__d : Equality.sort Y),
@size (Equality.sort X) xs = @size (Equality.sort Y) ys ->
(exists idx : nat,
   is_true (idx < @size (Equality.sort X) xs) /\
   @nth (Equality.sort X) x__d xs idx = x /\ @nth (Equality.sort Y) y__d ys idx = y) ->
is_true ((x, y) \in @zip (Equality.sort X) (Equality.sort Y) xs ys)

in_zip is not universe polymorphic
Arguments in_zip {X Y} (xs ys)%seq_scope x x__d y y__d _ _
in_zip is opaque
Expands to: Constant prosa.util.list.in_zip
Declared in library prosa.util.list, line 399, characters 6-12
@in_zip
     : forall (X Y : eqType) (xs : seq (Equality.sort X)) (ys : seq (Equality.sort Y))
         (x x__d : Equality.sort X) (y y__d : Equality.sort Y),
       @size (Equality.sort X) xs = @size (Equality.sort Y) ys ->
       (exists idx : nat,
          is_true (idx < @size (Equality.sort X) xs) /\
          @nth (Equality.sort X) x__d xs idx = x /\ @nth (Equality.sort Y) y__d ys idx = y) ->
       is_true ((x, y) \in @zip (Equality.sort X) (Equality.sort Y) xs ys)
```

## Lean

```lean
@Prosa.Util.List.in_zip : ∀ {X : Type u_1} {Y : Type u_2} [DecidableEq X] [DecidableEq Y] (xs : List X) (ys : List Y)
  (x xDefault : X) (y yDefault : Y),
  xs.length = ys.length →
    (∃ idx, idx < xs.length ∧ xs.getD idx xDefault = x ∧ ys.getD idx yDefault = y) → (x, y) ∈ xs.zip ys
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_in_zip
     : forall X Y : Type,
       DecidableEq X ->
       DecidableEq Y ->
       forall (xs : List X) (ys : List Y) (x xDefault : X) (y yDefault : Y),
       @eq Nat (List_length X xs) (List_length Y ys) ->
       Exists Nat
         (fun idx : Nat =>
          And (LT_lt_inst1 Nat instLTNat idx (List_length X xs))
            (And (@eq X (List_getD X xs idx xDefault) x) (@eq Y (List_getD Y ys idx yDefault) y))) ->
       Membership_mem (Prod X Y) (List (Prod X Y)) (List_instMembership (Prod X Y)) 
         (List_zip X Y xs ys) (Prod_mk X Y x y)
```
