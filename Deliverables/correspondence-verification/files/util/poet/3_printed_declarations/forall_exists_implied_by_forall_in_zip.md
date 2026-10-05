# `forall_exists_implied_by_forall_in_zip`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.poet.forall_exists_implied_by_forall_in_zip`
- Lean: `Prosa.Util.Poet.forall_exists_implied_by_forall_in_zip`
- Certificate: `forall_exists_implied_by_forall_in_zip_statement_certificate`

## Official Rocq

```coq
forall_exists_implied_by_forall_in_zip :
forall {X Y : eqType} (P_bool : Equality.sort X * Equality.sort Y -> bool)
  (P_prop : Equality.sort X -> Equality.sort Y -> Prop) (xs : seq (Equality.sort X)),
(forall (x : Equality.sort X) (y : Equality.sort Y), is_true (P_bool (x, y)) <-> P_prop x y) ->
(exists ys : seq (Equality.sort Y),
   @size (Equality.sort X) xs = @size (Equality.sort Y) ys /\
   is_true
     (@all (Equality.sort X * Equality.sort Y) P_bool (@zip (Equality.sort X) (Equality.sort Y) xs ys) ==
      true)) ->
forall x : Equality.sort X, is_true (x \in xs) -> exists y : Equality.sort Y, P_prop x y

forall_exists_implied_by_forall_in_zip is not universe polymorphic
Arguments forall_exists_implied_by_forall_in_zip {X Y} (P_bool P_prop)%function_scope 
  xs%seq_scope _%function_scope _ x _
forall_exists_implied_by_forall_in_zip is opaque
Expands to: Constant prosa.util.poet.forall_exists_implied_by_forall_in_zip
Declared in library prosa.util.poet, line 12, characters 6-44
@forall_exists_implied_by_forall_in_zip
     : forall (X Y : eqType) (P_bool : Equality.sort X * Equality.sort Y -> bool)
         (P_prop : Equality.sort X -> Equality.sort Y -> Prop) (xs : seq (Equality.sort X)),
       (forall (x : Equality.sort X) (y : Equality.sort Y), is_true (P_bool (x, y)) <-> P_prop x y) ->
       (exists ys : seq (Equality.sort Y),
          @size (Equality.sort X) xs = @size (Equality.sort Y) ys /\
          is_true
            (@all (Equality.sort X * Equality.sort Y) P_bool (@zip (Equality.sort X) (Equality.sort Y) xs ys) ==
             true)) ->
       forall x : Equality.sort X, is_true (x \in xs) -> exists y : Equality.sort Y, P_prop x y
```

## Lean

```lean
@Prosa.Util.Poet.forall_exists_implied_by_forall_in_zip : ∀ {X : Type u_1} {Y : Type u_2} [DecidableEq X]
  [DecidableEq Y] (PBool : X × Y → Bool) (PProp : X → Y → Prop) (xs : List X),
  (∀ (x : X) (y : Y), PBool (x, y) = true ↔ PProp x y) →
    (∃ ys, xs.length = ys.length ∧ (xs.zip ys).all PBool = true) → ∀ (x : X), x ∈ xs → ∃ y, PProp x y
```

## Lean, imported into Rocq

```coq
Prosa_Util_Poet_forall_exists_implied_by_forall_in_zip
     : forall X Y : Type,
       DecidableEq X ->
       DecidableEq Y ->
       forall (PBool : Prod X Y -> Bool) (PProp : X -> Y -> SProp) (xs : List X),
       (forall (x : X) (y : Y), Iff (@eq Bool (PBool (Prod_mk X Y x y)) Bool_true) (PProp x y)) ->
       Exists (List Y)
         (fun ys : List Y =>
          And (@eq Nat (List_length X xs) (List_length Y ys))
            (@eq Bool (List_all (Prod X Y) (List_zip X Y xs ys) PBool) Bool_true)) ->
       forall x : X,
       Membership_mem X (List X) (List_instMembership X) xs x -> Exists Y (fun y : Y => PProp x y)
```
