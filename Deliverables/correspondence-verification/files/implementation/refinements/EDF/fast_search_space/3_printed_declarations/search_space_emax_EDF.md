# `search_space_emax_EDF`

- Kind (Rocq): Definition
- Rocq: `prosa.implementation.refinements.EDF.fast_search_space.search_space_emax_EDF`
- Lean: `Prosa.Implementation.Refinements.EDF.FastSearchSpace.search_space_emax_EDF`
- Certificate: `search_space_emax_EDF_correspondence`

## Official Rocq

```coq
search_space_emax_EDF : seq (Equality.sort Task) -> Equality.sort Task -> nat -> seq nat

search_space_emax_EDF is not universe polymorphic
Arguments search_space_emax_EDF ts%_seq_scope tsk L%_nat_scope
search_space_emax_EDF is transparent
Expands to: Constant prosa.implementation.refinements.EDF.fast_search_space.search_space_emax_EDF
Declared in library prosa.implementation.refinements.EDF.fast_search_space, line 79, characters 13-34
search_space_emax_EDF
     : seq (Equality.sort Task) -> Equality.sort Task -> nat -> seq nat
```

Body:

```coq
search_space_emax_EDF =
fun (ts : seq (Equality.sort Task)) (tsk : Equality.sort Task) (L : nat) =>
\cat_(tsko<-ts)task_search_space_emax_EDF tsk tsko L
     : seq (Equality.sort Task) -> Equality.sort Task -> nat -> seq nat

Arguments search_space_emax_EDF ts%_seq_scope tsk L%_nat_scope
```

## Lean

```lean
Prosa.Implementation.Refinements.EDF.FastSearchSpace.search_space_emax_EDF : List
    Prosa.Implementation.Refinements.EDF.FastSearchSpace.Task →
  Prosa.Implementation.Refinements.EDF.FastSearchSpace.Task → ℕ → List ℕ
```

Body:

```lean
def Prosa.Implementation.Refinements.EDF.FastSearchSpace.search_space_emax_EDF : List
    Prosa.Implementation.Refinements.EDF.FastSearchSpace.Task →
  Prosa.Implementation.Refinements.EDF.FastSearchSpace.Task → ℕ → List ℕ :=
fun ts tsk L =>
  Prosa.Util.Bigcat.bigCatSeqAll ts fun tsko =>
    Prosa.Implementation.Refinements.EDF.FastSearchSpace.task_search_space_emax_EDF tsk tsko L
```

## Lean, imported into Rocq

```coq
Prosa_Implementation_Refinements_EDF_FastSearchSpace_search_space_emax_EDF
     : List_inst1 Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task ->
       Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task -> Nat -> List_inst1 Nat
```

Body:

```coq
Prosa_Implementation_Refinements_EDF_FastSearchSpace_search_space_emax_EDF@{} =
fun (ts : List_inst1 Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task)
  (tsk : Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task) (L : Nat) =>
Prosa_Util_Bigcat_bigCatSeqAll_inst3 Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task Nat ts
  (fun tsko : Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task =>
   Prosa_Implementation_Refinements_EDF_FastSearchSpace_task_search_space_emax_EDF tsk tsko L)
     : List_inst1 Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task ->
       Prosa_Implementation_Refinements_EDF_FastSearchSpace_Task -> Nat -> List_inst1 Nat

Arguments Prosa_Implementation_Refinements_EDF_FastSearchSpace_search_space_emax_EDF ts tsko s%_Nat_scope
```
