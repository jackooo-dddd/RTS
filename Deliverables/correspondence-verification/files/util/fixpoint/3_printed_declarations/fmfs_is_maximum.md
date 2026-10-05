# `fmfs_is_maximum`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.fixpoint.fmfs_is_maximum`
- Lean: `Prosa.Util.Fixpoint.fmfs_is_maximum`
- Certificate: `fixpoint_fmfs_maximum_statement_certificate`

## Official Rocq

```coq
fmfs_is_maximum :
forall (f : nat -> nat -> nat) (sp : seq nat) (h s r : nat),
@Some nat r = find_max_fixpoint_of_seq f sp h ->
is_true (s \in sp) -> exists2 v : nat, @Some nat v = find_fixpoint (f s) h & is_true (v <= r)

fmfs_is_maximum is not universe polymorphic
Arguments fmfs_is_maximum f%function_scope sp%seq_scope (h s r)%nat_scope _ _
fmfs_is_maximum is opaque
Expands to: Constant prosa.util.fixpoint.fmfs_is_maximum
Declared in library prosa.util.fixpoint, line 238, characters 6-21
fmfs_is_maximum
     : forall (f : nat -> nat -> nat) (sp : seq nat) (h s r : nat),
       @Some nat r = find_max_fixpoint_of_seq f sp h ->
       is_true (s \in sp) -> exists2 v : nat, @Some nat v = find_fixpoint (f s) h & is_true (v <= r)
```

## Lean

```lean
Prosa.Util.Fixpoint.fmfs_is_maximum : ∀ (f : ℕ → ℕ → ℕ) (sp : List ℕ) (h s r : ℕ),
  some r = Prosa.Util.Fixpoint.find_max_fixpoint_of_seq f sp h →
    s ∈ sp → ∃ v, some v = Prosa.Util.Fixpoint.find_fixpoint (f s) h ∧ v ≤ r
```

## Lean, imported into Rocq

```coq
Prosa_Util_Fixpoint_fmfs_is_maximum
     : forall (f : Nat -> Nat -> Nat) (sp : List_inst1 Nat) (h s r : Nat),
       @eq (Option_inst1 Nat) (Option_some_inst1 Nat r) (Prosa_Util_Fixpoint_find_max_fixpoint_of_seq f sp h) ->
       Membership_mem_inst3 Nat (List_inst1 Nat) (List_instMembership_inst1 Nat) sp s ->
       Exists Nat
         (fun v : Nat =>
          And (@eq (Option_inst1 Nat) (Option_some_inst1 Nat v) (Prosa_Util_Fixpoint_find_fixpoint (f s) h))
            (LE_le_inst1 Nat instLENat v r))
```
