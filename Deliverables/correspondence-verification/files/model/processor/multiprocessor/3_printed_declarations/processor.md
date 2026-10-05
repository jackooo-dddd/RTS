# `processor`

- Kind (Rocq): Definition
- Rocq: `prosa.model.processor.multiprocessor.processor`
- Lean: `Prosa.Model.Processor.Multiprocessor.processor`
- Certificate: `processor_source_total, processor_target_total`

## Official Rocq

```coq
processor : nat -> predArgType

processor is not universe polymorphic
Arguments processor num_cpus%nat_scope
processor is transparent
Expands to: Constant prosa.model.processor.multiprocessor.processor
Declared in library prosa.model.processor.multiprocessor, line 33, characters 13-22
processor
     : nat -> predArgType
```

Body:

```coq
processor = [eta ordinal]
     : nat -> predArgType

Arguments processor num_cpus%nat_scope
```

## Lean

```lean
Prosa.Model.Processor.Multiprocessor.processor : ℕ → Type
```

Body:

```lean
@[reducible] def Prosa.Model.Processor.Multiprocessor.processor : ℕ → Type :=
fun num_cpus => Fin num_cpus
```

## Lean, imported into Rocq

```coq
Prosa_Model_Processor_Multiprocessor_processor
     : Nat -> Type
```

Body:

```coq
Prosa_Model_Processor_Multiprocessor_processor@{} = fun num_cpus : Nat => Fin num_cpus
     : Nat -> Type

Arguments Prosa_Model_Processor_Multiprocessor_processor n%_Nat_scope
```
