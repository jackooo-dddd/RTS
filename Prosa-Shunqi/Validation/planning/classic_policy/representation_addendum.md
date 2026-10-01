# Classic representation addendum

Status: approved by the user on 2026-10-01 (Stage 0 of
`classic-prosa/casestudy-translation/README.md`). It extends
`Validation/planning/v06_current_policy/representation_policy.md` for the classic validation family
(ProsaBuddy classic Prosa, commit `f692cb7`) and does not change any v0.6 rule. Where this file is
silent, the v0.6 policy applies unchanged.

## Authority

- The semantic target is the pinned ProsaBuddy checkout `Validation/.work/prosabuddy-f692cb7`
  (`prosaworkspace/classic/…`, plus the official v0.6 `util/` it imports), and the elaborated type of
  each declaration printed in ProsaBuddy's own toolchain, the opam switch `prosa-0.6` (Rocq 9.0.1,
  MathComp 2.4). The evidence is in `planning/classic_dependency/declaration_type_evidence.json`,
  produced by `scripts/classic_reference_evidence.py`.
- The validation toolchain is the v0.6 one (Rocq 9.3+rc1, MathComp 2.6). Classic source files are
  compiled there unchanged, with the recorded compatibility prelude
  `classic-prosa/rocq93-port/Rocq90Compat.v` (`-ri Compat.Rocq90Compat`). The prelude restores two
  Rocq 9.0 defaults (`SsrOldRewriteGoalsOrder` and the 9.0 `intuition_solver`); it changes no
  statement and no source byte. The official v0.6 `util/` files are compiled exactly as in the v0.6
  chain, with the recorded v0.6 proof-only patches.
- The pinned util files are byte-identical to the v0.6 pins, so the accepted v0.6 Lean modules
  `Prosa.Util.*` are reused; a classic run checks every reused v0.6 artifact against its v0.6
  manifest.

## Rules

| Classic source | Lean | First used at rank |
|---|---|---|
| `Module M. … End M.` inside a file | nested Lean namespace: file path namespace, then `M` (`Prosa.Classic.Model.Time.Time`) | 1 |
| `Definition time := nat` and its aliases | `abbrev … := Nat` | 1 |
| `Context {T : eqType}` | carrier + `[DecidableEq T]`, as in v0.6 | 4 |
| model parameters passed as functions (`job_cost : Job -> time`, `task_period : sporadic_task -> time`, …) | explicit function arguments, in the same position; never type classes | 22 |
| `taskset_of T := seq_of T` (a `{set}` sequence) | v0.6 `Prosa.Util.Seqset.set T` (ordered list + `Nodup`); `count P ts` is `ts.val.countP P` | 22 |
| global schedule `schedule Job num_cpus := processor num_cpus -> time -> option Job` | the same function type, processors `'I_num_cpus` as `Fin num_cpus` | 27 |
| APA affinity `{set processor num_cpus}` | v0.6 `Prosa.Util.Seqset.set (Fin num_cpus)`; `#|A|` is `(Finset.univ.filter (· ∈ A)).card` | 29 |
| `[exists x in 'I_n, P x]`, `[exists x, P x]` over `'I_n` | `(List.finRange n).any P` | 11 |
| `\sum_(i < n) F i` | `∑ i : Fin n, F i` | 13 |
| `\sum_(a <= t < b) F t` | `∑ t ∈ Finset.Ico a b, F t` | 13 |
| `\sum_(x <- s) F x`, `\sum_(x <- s \| P x) F x` | v0.6 `sumSeq s F`, `sumFiltered s P F`; a pair pattern `\sum_((a, b) <- s)` is `fun (a, b) => …` | 20 |
| `sort leT s` | `s.mergeSort leT` (both stable; equal on the total preorders used) | 25 |
| section `Let`s | unfolded in statements; a `Let` used by a definition is inlined into its body | 1 |
| Ltac-only files (`ssromega.v`, most of `tactics.v`) | no Lean declarations | — |

Binder lists follow the Rocq contract after sections close (`About`/`Check`): a declaration takes
exactly the section variables and hypotheses Rocq abstracts, in Rocq's order, with Rocq's
implicitness. Rocq abstracts every section hypothesis that a proof script mentions, so some binders
are unused in Lean; this is recorded per file, never repaired by dropping the binder.

## Known boundaries to watch

- `∑ i : Fin n` and `Finset.Ico` sums in statements need the v0.6 export normalizations
  (Finset.Ico projection; for `Fin` sums the multiprocessor-file approach) or the Rocq import can
  stall. Decide per file, with the actual export.
- The case-study statement files (RTS_Papers) are outside this addendum; their known source issues
  (swapped `constrained_deadline_model` arguments, an iff-stated theorem, a `[seq fst p <- …]` typo)
  are recorded in the case-study README and are not repaired by translation.
