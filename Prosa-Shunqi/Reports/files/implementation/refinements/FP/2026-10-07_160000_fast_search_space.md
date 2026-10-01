# implementation/refinements/FP/fast_search_space.v — canonical translation report

First experiment timestamp: **2026-10-07 16:00:00 +08:00**

The seventh file behind the CoqEAL build boundary. It uses the same local CoqEAL 2.1.2 build and official-toolchain
type evidence as `refinements.v`. That report covers CoqEAL's provenance and how the evidence was produced.

## Authority and scope

- Prosa v0.6 `414e667…`; `implementation/refinements/FP/fast_search_space.v`; layer 27; rank 354.
- **10 public declarations:**
  - 9 definitions: `ohep_task`, `total_hep_rbf`, `total_ohep_rbf`, `check_point_FP`, `blocking_bound_NP`,
    `check_point_NP`, `correct_search_space`, `search_space_emax_FP_h`, `search_space_emax_FP`;
  - the `Prop` lemma `search_space_subset_FP`.
- **Dependencies (accepted):** `implementation/refinements/fast_search_space_computation.v` and
  `results/rta/ideal/fp/bounded_nps.v`.

## Translation

`Prosa/Implementation/Refinements/FP/FastSearchSpace.lean` compiles with only the standard Lean axioms. Five
declarations use no axiom.

- **The policy.** The file-wide `#[local] Existing Instance NumericFPAscending` is the accepted
  `NumericFPAscending Task`, passed explicitly.
- **Filtered sums and maxima.** `\sum_(x <- xs | P x) F x` and `\max_(x <- xs | P x) F x` are the accepted
  `sumFiltered`/`maxFiltered`.
- **Representation** (as in `FastSearchSpaceComputation`):
  - `a != b` is `decide (a ≠ b)`;
  - `[seq A <- s | p A]` is `s.filter p`;
  - `iota`, `muln`, `predn` and `ε` as in that file.
- **Search space.** `is_in_search_space` is the accepted `Prosa.Results.Rta.Ideal.Fp.BoundedPi.is_in_search_space`.
- **`search_space_subset_FP`** follows the source. Membership in the filtered search space gives `A < L` and a
  change of the request-bound function. The accepted `task_search_space_subset` then places `A` in the
  computation-oriented search space, which is the accepted `search_space_arrival_curve_prefix_FP` by definition.

## Source binding

Source mode `official_closure`, with the run's CoqEAL build.
- **Closure:** `Validation/tooling/proof_closure/refinements_FP_fast_search_space_closure.txt`.
- **Patch:** `…-refinements-FP_fast_search_space.patch`, proof-only. The module itself is compiled byte-identically.

### Type fingerprints

10/10 match the official-toolchain evidence:
- **3 `EXACT_MODULO_DEPENDENCY_MODULE_QUALIFIER`:** `ohep_task`, `total_hep_rbf`, `total_ohep_rbf`, with the
  `task.Task` qualifier.
- **7 `EXACT_MODULO_DEPENDENCY_AND_OWN_MODULE_QUALIFIER`:** the `task.Task` qualifier together with this file's own
  qualifier `FP.fast_search_space.` (the EDF file declares the same names):
  - at the head of the six definitions that share a name with `EDF/fast_search_space.v`;
  - inside `search_space_subset_FP`, on `correct_search_space` and `search_space_emax_FP`. The spec lists these two
    in `own_qualified_in_type`.

### Pipeline addition (opt-in)

`translation_file_pipeline.py`, in the opt-in `dependency_qualified_in_type` branch: after the dependency repairs,
the own-module qualifiers accepted by the existing rules may also be removed. These are:
- the display qualifier at the head;
- for the names in `own_qualified_in_type`, the qualifier inside the type.

The result is recorded as `EXACT_MODULO_DEPENDENCY_AND_OWN_MODULE_QUALIFIER`. Each repair is exactly one of the
accepted rules, and specs without the field are unchanged.

## Validation

- **Spec:** `implementation_refinements_FP_fast_search_space.json`.
- **Lean base run:** `implementation_refinements_fast_search_space_computation_final`.
- **Accepted oleans.** The base adds the 66 accepted oleans of the `results/rta/ideal/fp/bounded_nps` closure that
  the base run lacked. Each is checked against its accepted manifest (`extra_olean_artifacts`).
- **Export:** 36,473 lines. Its root is the file's 9 definitions with bodies and its statement statement-only,
  plus:
  - the base refinements set;
  - the accepted task, arrival-curve and fast-search-space refinement definitions;
  - the concrete task and job definitions with their projections;
  - the accepted `sumFiltered`/`maxFiltered`/`sumSeq`.

### Certificate chain (7 modules)

- **The 6 re-bound modules:** `RfpBase`, `RfpArrivalBound`, `RfpTask`, `RfpArrivalCurve`, `RfpArrivalCurvePrefix`
  and `RfpFastSearchSpaceComputation`. These are the accepted certificates of the six refinements dependencies,
  re-bound to this export without their statement correspondences.
- **Pruning.** They are pruned across the chain. This drops the commands listed in the `arrival_curve_prefix.v` and
  `fast_search_space_computation.v` reports, except that `rf_sumFiltered_ex` is kept here, since its constants are
  in this export.
- **Every kept command is unchanged.**
- **`RefFPFastSearchSpaceCorrespondence.v` (new, about 330 lines):**
  - **Element-mapped sum and maximum.** The accepted filtered-sum and filtered-maximum correspondences are
    generalised from the identity carrier to an element map (here the concrete task map), with the same proofs.
  - **`maxn` and Lean's `max`.** This export reaches Lean's `max` on `Nat` through `maxOfLe` (an `ite` on `≤`), not
    `Nat.max`. MathComp `maxn` is related to it directly (`rf_maxL_ex`).
  - **Boolean negation** against `Not`.
  - **Policy and request-bound function.** The policy `NumericFPAscending` (`task_priority tsk2 <= task_priority
    tsk1`) and the concrete request-bound function are related through the importer's concrete-instance copies
    (`…_inst1`).
  - **The 9 definitions** are each related for related inputs: tasks by `TaskRel`, task lists and numbers by the
    canonical maps, pairs componentwise.
  - **`search_space_subset_FP`** is related by `PropSPropRel`, composed from the accepted combinators.
- **No certificate uses its own source or target theorem.** Statement types are taken with `type of`.
- **Audit:** 10 certificates.
  - 9 are `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` and 1 is `CERTIFIED`;
  - `semantic_premises=[]` and `unexpected=[]`;
  - no statement-only dependency;
  - no source or target theorem dependency;
  - `sorryAx` does not occur in the export.

### Attempts

- **Prepare attempt 1:** passed. `check` and `publish` also passed on their first runs.

## Formal acceptance

Coverage **350 / 357 files**, **2344 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
