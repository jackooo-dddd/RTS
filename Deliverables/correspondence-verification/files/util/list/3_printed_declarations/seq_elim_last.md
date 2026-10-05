# `seq_elim_last`

- Kind (Rocq): Lemma
- Rocq: `prosa.util.list.seq_elim_last`
- Lean: `Prosa.Util.List.seq_elim_last`
- Certificate: `seq_elim_last_statement_certificate`

## Official Rocq

```coq
seq_elim_last :
forall {X : Type} (n : nat) (xs : seq X),
@size X xs = n.+1 -> exists (x : X) (xs__c : seq X), xs = xs__c ++ [:: x] /\ @size X xs__c = n

seq_elim_last is not universe polymorphic
Arguments seq_elim_last {X}%type_scope n%nat_scope xs%seq_scope _
seq_elim_last is opaque
Expands to: Constant prosa.util.list.seq_elim_last
Declared in library prosa.util.list, line 320, characters 6-19
@seq_elim_last
     : forall (X : Type) (n : nat) (xs : seq X),
       @size X xs = n.+1 -> exists (x : X) (xs__c : seq X), xs = xs__c ++ [:: x] /\ @size X xs__c = n
```

## Lean

```lean
@Prosa.Util.List.seq_elim_last : ∀ {T : Type u_1} (n : ℕ) (xs : List T),
  xs.length = n + 1 → ∃ x pre, xs = pre ++ [x] ∧ pre.length = n
```

## Lean, imported into Rocq

```coq
Prosa_Util_List_seq_elim_last
     : forall (T : Type) (n : Nat) (xs : List T),
       @eq Nat (List_length T xs)
         (HAdd_hAdd_inst7 Nat Nat Nat (instHAdd_inst1 Nat instAddNat) n
            (OfNat_ofNat_inst1 Nat 1 (instOfNatNat 1))) ->
       Exists T
         (fun x : T =>
          Exists (List T)
            (fun pre : List T =>
             And
               (@eq (List T) xs
                  (HAppend_hAppend (List T) (List T) (List T)
                     (instHAppendOfAppend (List T) (List_instAppend T)) pre (List_cons T x (List_nil T))))
               (@eq Nat (List_length T pre) n)))
```
