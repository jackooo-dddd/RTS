# `in_cat`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.in_cat`
- Lean: `Prosa.Util.List.in_cat`
- Certificate: `in_cat_statement_certificate`

## Official Rocq

```coq
in_cat :
forall {X : eqType} (x : Equality.sort X) (xs : seq (Equality.sort X)),
is_true (x \in xs) -> exists xsl xsr : seq (Equality.sort X), xs = xsl ++ [:: x] ++ xsr

in_cat is not universe polymorphic
Arguments in_cat {X} x xs%seq_scope _
in_cat is opaque
Expands to: Constant prosa.util.list.in_cat
Declared in library prosa.util.list, line 342, characters 6-12
@in_cat
     : forall (X : eqType) (x : Equality.sort X) (xs : seq (Equality.sort X)),
       is_true (x \in xs) -> exists xsl xsr : seq (Equality.sort X), xs = xsl ++ [:: x] ++ xsr
```

## Lean

```lean
@Prosa.Util.List.in_cat : ∀ {T : Type u_1} [DecidableEq T] (x : T) (xs : List T),
  x ∈ xs → ∃ left right, xs = left ++ [x] ++ right
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_in_cat
     : forall T : Type,
       DecidableEq T ->
       forall (x : T) (xs : List T),
       Membership_mem T (List T) (List_instMembership T) xs x ->
       Exists (List T)
         (fun left : List T =>
          Exists (List T)
            (fun right : List T =>
             xs =
             HAppend_hAppend (List T) (List T) (List T) (instHAppendOfAppend (List T) (List_instAppend T))
               (HAppend_hAppend (List T) (List T) (List T) (instHAppendOfAppend (List T) (List_instAppend T))
                  left (List_cons T x (List_nil T)))
               right))
```
