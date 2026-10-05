# `eps_sbf`

- Kind (Rocq): Definition
- Rocq: `prosa.analysis.facts.model.exceedance.SBF.eps_sbf`
- Lean: `Prosa.Analysis.Facts.Model.Exceedance.SBF.eps_sbf`
- Certificate: `eps_sbf_correspondence`

## Official Rocq

```coq
eps_sbf : work -> nat -> work

eps_sbf is not universe polymorphic
Arguments eps_sbf e Δ%nat_scope
eps_sbf is transparent
Expands to: Constant prosa.analysis.facts.model.exceedance.SBF.eps_sbf
Declared in library prosa.analysis.facts.model.exceedance.SBF, line 15, characters 13-20
eps_sbf
     : work -> nat -> work
```

Body:

```coq
eps_sbf = fun e : work => subn^~ e
     : work -> nat -> work

Arguments eps_sbf e Δ%nat_scope
```

## Lean

```lean
Prosa.Analysis.Facts.Model.Exceedance.SBF.eps_sbf : Prosa.Behavior.Job.work → ℕ → Prosa.Behavior.Job.work
```

Body:

```lean
def Prosa.Analysis.Facts.Model.Exceedance.SBF.eps_sbf : Prosa.Behavior.Job.work → ℕ → Prosa.Behavior.Job.work :=
fun e Δ => Δ - e
```

## Lean, imported into Rocq

```coq
Prosa_Analysis_Facts_Model_Exceedance_SBF_eps_sbf
     : Prosa_Behavior_Job_work -> Nat -> Prosa_Behavior_Job_work
```

Body:

```coq
Prosa_Analysis_Facts_Model_Exceedance_SBF_eps_sbf@{} =
fun (e : Prosa_Behavior_Job_work) (_UU0394_ : Nat) =>
HSub_hSub_inst7 Nat Prosa_Behavior_Job_work Nat (instHSub_inst1 Nat instSubNat) _UU0394_ e
     : Prosa_Behavior_Job_work -> Nat -> Prosa_Behavior_Job_work

Arguments Prosa_Analysis_Facts_Model_Exceedance_SBF_eps_sbf e _UU0394_%_Nat_scope
```
