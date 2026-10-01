# implementation/refinements/EDF/fast_search_space.v — canonical translation report

First experiment timestamp: **2026-10-07 17:00:00 +08:00**

The eighth file behind the CoqEAL build boundary. It uses the same local CoqEAL 2.1.2 build and official-toolchain
type evidence as `refinements.v`. That report covers CoqEAL's provenance and how the evidence was produced.

## Authority and scope

- Prosa v0.6 `414e667…`; `implementation/refinements/EDF/fast_search_space.v`; layer 28; rank 355.
- **14 public declarations:**
  - 4 definitions over the refinements `Task`: `bound_on_total_hep_workload`, `check_point_FP`,
    `blocking_bound_NP`, `check_point_NP`;
  - the section's own aliases `Task` and `Job`;
  - 6 search-space definitions: `correct_search_space`, `search_space_emax_FP_h`, `search_space_emax_FP`,
    `task_search_space_emax_EDF_h`, `task_search_space_emax_EDF`, `search_space_emax_EDF`;
  - 2 `Prop` lemmas: `EDF_ss_generalize_FP_ss` and `search_space_subset_EDF`.
- **Dependencies (accepted):** `implementation/refinements/fast_search_space_computation.v` and
  `results/rta/ideal/edf/bounded_nps.v`.

## Translation

`Prosa/Implementation/Refinements/EDF/FastSearchSpace.lean` compiles with only the standard Lean axioms. Nine
declarations use no axiom.

- **Type aliases.**
  - The four definitions before the section are over the accepted `Prosa.Implementation.Refinements.Task.Task`.
  - The section's own `Task`/`Job` (the concrete types as `eqType`s) are abbreviations of the accepted concrete
    types.
- **Section instances.**
  - The section's `#[local] Existing Instance ConcreteMaxArrivals` is the accepted global instance.
  - The section's `Context TMNSP` is used by no definition, so, as in the elaborated types, no declaration takes it.
- **Representation:**
  - `\sum`/`\max` with a filter are the accepted `sumFiltered`/`maxFiltered`;
  - `\cat_(x <- xs) F x` is the accepted `bigCatSeqAll`;
  - `[seq i | i <- ts]` is `ts.map (fun i => i)`;
  - `minn` is `min`;
  - `shift_points_pos`/`shift_points_neg` are the accepted ones;
  - `i.-1` is `Nat.pred`;
  - `is_in_search_space` is the accepted EDF `BoundedNps.is_in_search_space`;
  - `head (0, 0) s` is `s.headD (0, 0)`;
  - the remaining notation is as in `FastSearchSpaceComputation`.
- **Proofs** follow the source:
  - **`EDF_ss_generalize_FP_ss`:** shifting forward and then backward by the same deadline is the identity (a
    private lemma `shift_neg_pos`).
  - **`search_space_subset_EDF`**, if the task's own request-bound function changes at `A`: `A` is in the task's own
    search space, which is the fixed-priority one, by the accepted `task_search_space_subset`.
  - **`search_space_subset_EDF`**, if the bound for another task `tsko` changes:
    - the change gives `D_tsko ≤ A + D_tsk`, since otherwise both arguments are `0`;
    - with `B = A + D_tsk − D_tsko`, `tsko`'s request-bound function changes at `B < L + (D_tsk − D_tsko)`;
    - the accepted `task_search_space_subset` and `nonshifted_offsets_are_positive` give the point `B + 1` in
      `tsko`'s repeated steps;
    - after the forward and backward shifts, that point is `A + 1`.
- **Local macro:** `omega'`, as in the accepted files.

## Source binding

Source mode `official_closure`, with the run's CoqEAL build.
- **Closure:** `Validation/tooling/proof_closure/refinements_EDF_fast_search_space_closure.txt`.
- **Patch:** `…-refinements-EDF_fast_search_space.patch`, proof-only. It also adds
  `Set SsrOldRewriteGoalsOrder.` to the module.
- **Module change:** the spec opts in with `official_closure.module_change: "rewrite_goals_order_flag"`. It is
  checked line by line and recorded in the manifest.

### Type fingerprints

14/14 are `EXACT_HASH`. The official evidence prints this file's `Task` unqualified, and the validation context
prints the same.

## Validation

- **Spec:** `implementation_refinements_EDF_fast_search_space.json`.
- **Lean base run:** `implementation_refinements_FP_fast_search_space_final`.
- **Accepted oleans.** The base adds the accepted oleans of the `results/rta/ideal/edf/bounded_nps` closure (14 new,
  plus the FP base's 66). Each is checked against its accepted manifest.
- **Export:** 36,718 lines. Its root is the file's 12 definitions with bodies and its 2 statements statement-only,
  plus:
  - the base refinements set;
  - the accepted task, arrival-curve and fast-search-space refinement definitions;
  - the concrete task and job definitions with their projections.

### Certificate chain (7 modules)

- **The 6 re-bound modules:** `ReBase` … `ReFastSearchSpaceComputation`. These are the accepted certificates of the
  six refinements dependencies, re-bound to this export without their statement correspondences, and pruned across
  the chain as for `FP/fast_search_space.v`.
- **Every kept command is unchanged.**
- **`RefEDFFastSearchSpaceCorrespondence.v` (new, about 420 lines):**
  - **Restated components.** The generic components of the accepted `FP/fast_search_space.v` certificate, with the
    same proofs: element-mapped filtered sum and maximum, Boolean negation, and `maxn`.
  - **`minn`** against Lean's `min` on `Nat`, which is `minOfLe`.
  - **`\cat_(x <- xs)`** against the accepted `bigCatSeqAll` (`List.flatMap`).
  - **Principal totals** of the section's `Task`/`Job` aliases.
  - **The 12 definitions** are related for related inputs. The accepted EDF `is_in_search_space` is unfolded with
    `task_rbf_changes_at`, and `bound_on_total_hep_workload_changes_at` (a `has` over tasks) with the accepted
    `rf_has_ex`.
  - **`EDF_ss_generalize_FP_ss`:** an equality of lists, related through injectivity of the list map.
  - **`search_space_subset_EDF`:** composed from the accepted combinators.
- **No certificate uses its own source or target theorem.** Statement types are taken with `type of`.
- **Audit:** 16 certificates: 14 declarations, with the alias totals.
  - 11 are `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` and 5 are `CERTIFIED`;
  - `semantic_premises=[]` and `unexpected=[]`;
  - no statement-only dependency;
  - no source or target theorem dependency;
  - `sorryAx` does not occur in the export.

### Attempts

- **Prepare attempt 1:** passed. `check` and `publish` also passed on their first runs.

## Formal acceptance

Coverage **351 / 357 files**, **2358 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
