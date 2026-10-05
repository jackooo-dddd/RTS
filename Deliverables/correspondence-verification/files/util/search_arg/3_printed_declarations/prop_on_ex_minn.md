# `prop_on_ex_minn`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.search_arg.prop_on_ex_minn`
- Lean: `Prosa.Util.SearchArg.prop_on_ex_minn`
- Certificate: `prop_on_ex_minn_statement_certificate`

## Official Rocq

```coq
prop_on_ex_minn :
forall (P : nat -> Prop) (pred : nat -> bool) (ex0 : exists n : nat, is_true (pred n)),
P (@ex_minn pred ex0) ->
exists n : nat, P n /\ is_true (pred n) /\ (forall n' : nat, is_true (pred n') -> is_true (n <= n'))

prop_on_ex_minn is not universe polymorphic
Arguments prop_on_ex_minn (P pred)%function_scope ex _
prop_on_ex_minn is opaque
Expands to: Constant prosa.util.search_arg.prop_on_ex_minn
Declared in library prosa.util.search_arg, line 236, characters 6-21
prop_on_ex_minn
     : forall (P : nat -> Prop) (pred : nat -> bool) (ex0 : exists n : nat, is_true (pred n)),
       P (@ex_minn pred ex0) ->
       exists n : nat, P n /\ is_true (pred n) /\ (forall n' : nat, is_true (pred n') -> is_true (n <= n'))
```

## Lean

```lean
Prosa.Util.SearchArg.prop_on_ex_minn : ∀ (P : ℕ → Prop) (pred : ℕ → Bool) (ex : ∃ n, pred n = true),
  P (Nat.find ex) → ∃ n, P n ∧ pred n = true ∧ ∀ (n' : ℕ), pred n' = true → n ≤ n'
```

## Lean, imported into Rocq

```coq
Prosa_Util_SearchArg_prop_on_ex_minn
     : forall (P : Nat -> SProp) (pred : Nat -> Bool) (ex : Exists Nat (fun n : Nat => pred n = Bool_true)),
       P
         (Nat_find (fun n : Nat => pred n = Bool_true)
            (fun a : Nat => instDecidableEqBool (pred a) Bool_true) ex) ->
       Exists Nat
         (fun n : Nat =>
          And (P n)
            (And (@eq Bool (pred n) Bool_true)
               (forall n' : Nat, @eq Bool (pred n') Bool_true -> LE_le_inst1 Nat instLENat n n')))
```
