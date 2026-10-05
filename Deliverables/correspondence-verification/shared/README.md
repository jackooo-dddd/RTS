# Shared modules

Modules used by more than one file. Each file's `4_correspondence/shared.md` lists the ones it uses.

## Common certificates: [`certificates/common/`](certificates/common/)

These modules do not mention any particular file's Lean declarations, so every file uses them unchanged.

| Module | Content |
|---|---|
| [`BigcatCorrespondence.v`](certificates/common/BigcatCorrespondence.v) | Artifact-local adapter for the approved eqType/DecidableEq, Bool and ordered seq/List boundaries. |
| [`BigopCorrespondence.v`](certificates/common/BigopCorrespondence.v) | Artifact-local realization of the already approved Bool, eqType and seq/List representation relations for `ImportedBigop`. |
| [`DivModCorrespondence.v`](certificates/common/DivModCorrespondence.v) | Operation-level bridge for the exact `Nat.div`/`Nat.mod` interface exported from the compiled `Prosa.Util.Div_mod` artifact. |
| [`EqTypeCorrespondence.v`](certificates/common/EqTypeCorrespondence.v) | Canonical realization of the approved representation change `eqType` -> carrier `Type` plus imported Lean `DecidableEq`. |
| [`FixpointBaseCorrespondence.v`](certificates/common/FixpointBaseCorrespondence.v) | The option observation for the actual compiled Fixpoint artifact. |
| [`FixpointMaxOperations.v`](certificates/common/FixpointMaxOperations.v) | Operation-level correspondence for the actual Fixpoint artifact. |
| [`FixpointMaxTheoremCorrespondence.v`](certificates/common/FixpointMaxTheoremCorrespondence.v) | The guards use the actual compiled Lean theorem constants only to check exact types. |
| [`FixpointMonotoneCorrespondence.v`](certificates/common/FixpointMonotoneCorrespondence.v) | Proves or defines `fixpoint_target_le`, `fixpoint_target_lt`, `fixpoint_target_sub` and 15 more. |
| [`FixpointTheoremCorrespondence.v`](certificates/common/FixpointTheoremCorrespondence.v) | Exact compiled theorem-type guard. |
| [`JobEqTypeAdapter.v`](certificates/common/JobEqTypeAdapter.v) | Artifact-local realization of the approved representation boundary `eqType` -> carrier `Type` plus Lean `DecidableEq`. |
| [`LogicalRelation.v`](certificates/common/LogicalRelation.v) | The introduction rule for `PropSPropRel` |
| [`MinmaxCorrespondence.v`](certificates/common/MinmaxCorrespondence.v) | Artifact-local representation adapter for `util/minmax.v`. |
| [`NatSubCorrespondence.v`](certificates/common/NatSubCorrespondence.v) | Adapter for the operations that occur in the actual freshly imported `Prosa.Util.Nat` theorem types. |
| [`NondecreasingBaseAdapter.v`](certificates/common/NondecreasingBaseAdapter.v) | Proves or defines `nd_false_elim`, `nd_false_to_strict`, `nd_coq_false_to_target` and 23 more. |
| [`NondecreasingCorrespondence.v`](certificates/common/NondecreasingCorrespondence.v) | Artifact-local realization of the approved `seq nat <-> List Nat` relation. |
| [`PoetCorrespondence.v`](certificates/common/PoetCorrespondence.v) | Artifact-local realization of the already approved `eqType -> Type + DecidableEq` and `seq -> List` boundaries. |
| [`PropSPropFoundation.v`](certificates/common/PropSPropFoundation.v) | `PropSPropRel`, which pairs a Rocq `Prop` with an imported Lean `SProp`, with maps in both directions; also the single foundation axiom `interpret_strict` |
| [`RelListCorrespondence.v`](certificates/common/RelListCorrespondence.v) | Proves or defines `rel_false_elim`, `RelBoolTruth`, `RelBoolRel` and 20 more. |
| [`SeqsetCorrespondence.v`](certificates/common/SeqsetCorrespondence.v) | Proves or defines `seqset_false_elim`, `SeqsetBoolTruth`, `seqset_coq_false_to_imported` and 29 more. |
| [`SetoidCorrespondence.v`](certificates/common/SetoidCorrespondence.v) | Constructor-level correspondence for the actual source and imported inductives. |
| [`SubadditivityNatCorrespondence.v`](certificates/common/SubadditivityNatCorrespondence.v) | `SubNatRel`, relating Rocq `nat` and Lean `Nat`, with `+`, `*`, `≤`, `<` and `=` |
| [`SumIntervalCorrespondence.v`](certificates/common/SumIntervalCorrespondence.v) | Computational correspondence for the exact normalized finite-sum interface exported from the fresh compiled `Prosa.Util.Sum` artifact. |
| [`SumSequenceCorrespondence.v`](certificates/common/SumSequenceCorrespondence.v) | Namespace-local realization of the already approved semantic boundaries for the actual `ImportedSumSequence` artifact. lean4export seals every artifact in its own module, so its `List` and `Bool` … |
| [`SuperadditivityArithmeticCertificate.v`](certificates/common/SuperadditivityArithmeticCertificate.v) | Proves or defines `superadditivity_target_zero`, `superadditivity_first_zero_target_statement`, `superadditivity_first_zero_related` and 8 more. |
| [`SuperadditivityBaseCorrespondence.v`](certificates/common/SuperadditivityBaseCorrespondence.v) | The source bodies above are byte-identical computational declarations extracted from pinned v0.6; the target bodies are the actual compiled Lean definitions imported from Superadditivity.out. |
| [`SuperadditivityEquivalenceCertificate.v`](certificates/common/SuperadditivityEquivalenceCertificate.v) | The exact target theorem constant appears only in a separate type guard, never in the correspondence proof below. |
| [`SuperadditivityExtensionOperations.v`](certificates/common/SuperadditivityExtensionOperations.v) | Proves or defines `sa_list_to_imported`, `sa_list_to_rocq`, `SaListRel` and 30 more. |
| [`SuperadditivityHorizonCertificate.v`](certificates/common/SuperadditivityHorizonCertificate.v) | Proves or defines `sa_source_update`, `sa_update_hyp_related`, `sa_horizon_at_target_statement` and 5 more. |
| [`SuperadditivityMonotoneCertificate.v`](certificates/common/SuperadditivityMonotoneCertificate.v) | Proves or defines `superadditivity_target_le`, `superadditivity_target_decide_le`, `superadditivity_false_elim` and 8 more. |
| [`SupremumTheoremCorrespondence.v`](certificates/common/SupremumTheoremCorrespondence.v) | Proves or defines `sup_theorem_false_elim`, `sup_relation_false_elim`, `SupBoolTruth` and 34 more. |
| [`TypeSPropRelation.v`](certificates/common/TypeSPropRelation.v) | Some MathComp theorem statements expose an informative view (notably a universally quantified `reflect`) whose closed statement lives in `Type`. |
| [`UnitGrowthCorrespondence.v`](certificates/common/UnitGrowthCorrespondence.v) | Adapters for the operations occurring in the freshly imported `Prosa.Util.UnitGrowth` artifact. |

## Shared certificates: [`certificates/`](certificates/)

These modules state relations about imported Lean definitions. A module is placed here **only if at least two files of this folder use it**; a module used by a single file stays in that file's `4_correspondence/` folder.

Each translated file's Lean code is imported into Rocq as its own module, so a module used by several files mentions a different imported module in each. Each shared certificate has an **origin**: the first file, in the order of the file dependency graph (the translation order), whose certificates contain this text anywhere in the project. The text is stored once, as it appears in its origin. A file that uses it may differ only in the imported module name, the certificate module names in its `Require` lines, or the module's own name; that file's `shared.md` lists which. During validation each file's copy is compiled against that file's own import, so its proofs are checked again for every file.

**Naming.** A shared file is named after its module (`ArrivalsSeqOperations.v`). The same module name can have several different texts: when a later file reused a module but had to edit it (for example, cut parts that mention definitions its export does not contain, or add a helper it needs), the edited copy kept the original name. Storing both under one name would overwrite one with the other, so a file would link to a text it was never compiled with. The text whose origin comes first in dependency order keeps the plain name; later different texts are numbered `-2`, `-3`, … (`FactsEdfOptCorrespondence-2.v`).

[`certificates.csv`](certificates.csv) lists every shared certificate, one row per file:

| Column | Meaning |
|---|---|
| `shared file` | Path of the stored module, relative to this folder |
| `origin` | The first file, in dependency-graph order, whose certificates contain this text (across the whole project; it may be a file not yet in this folder) |
| `imported module in this copy` | The Lean code this stored text is about: its line `From FoundationImported Require Import <module>` loads the origin file's Lean translation into Rocq, and the proofs relate to those definitions. A file that reuses the certificate replaces this name with its own imported module (e.g. `ImportedService` becomes `ImportedFinishTime` in `analysis/definitions/finish_time.v`); its `shared.md` shows the replacement |
| `used by` | The files of this folder whose certificate chains use it, by rank, separated by `;` |
| `file names in using files` | Under which file name (without `.v`) each using file keeps its copy, as `name: files`, separated by `;`. In Rocq a module is one `.v` file, and other files load it by its file name |
| `sha256` | SHA-256 of the stored file, to check which exact text it is |
| `description` | The first sentence of the module's own opening comment |

**`used by` and `file names in using files`.** `used by` lists *which files* use the certificate; `file names in using files` says *what each of them calls its copy*. Each file keeps its own copy, and some saved it under another file name. The different names are only a naming convention from translation (a reusing file prefixed its copies with its own short name, e.g. `Jitter`, `Ps`), not a requirement: each file is validated in its own folder, so the original name would have worked as well. Example, the row of [`certificates/CurvesCorrespondence.v`](certificates/CurvesCorrespondence.v) (origin `model/task/arrival/curves.v`):

```text
CurvesCorrespondence: model/task/arrival/curves.v, model/composite/valid_task_arrival_sequence.v, model/task/arrival/curve_as_rbf.v, … (62 more);
OvhCurvesCorrespondence: analysis/facts/model/overheads/schedule_change_bound.v, analysis/facts/model/overheads/sbf/fifo.v, analysis/facts/model/overheads/sbf/fp.v, … (10 more);
ExcCurvesCorrespondence: results/rta/exc/fp/fully_nonpreemptive.v
```

The same pairing appears in each using file's `4_correspondence/shared.md`, in its `Module` column.

## Lean interfaces: [`lean_interfaces/`](lean_interfaces/)

Validation-only Lean equations and definitions, proved in Lean and exported with their proofs, that several files' exports include. Each interface used by at least one file of this folder is stored once.

[`lean_interfaces.csv`](lean_interfaces.csv) lists them, one row per interface:

| Column | Meaning |
|---|---|
| `interface` | Path of the Lean file, relative to this folder |
| `used by` | The files of this folder whose exports include it, by rank, separated by `;` |
| `description` | The interface's module comment; if it has none, its first doc comment; if it has neither, a generated summary: the Prosa module it is about, how many equations or definitions it contains, and their names |
