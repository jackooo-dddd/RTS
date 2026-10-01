# implementation/refinements/fast_search_space_computation.v — canonical translation report

First experiment timestamp: **2026-10-07 15:00:00 +08:00**

The sixth file behind the CoqEAL build boundary. It uses the same local CoqEAL 2.1.2 build and official-toolchain
type evidence as `refinements.v`. That report covers CoqEAL's provenance and how the evidence was produced.

## Authority and scope

- Prosa v0.6 `414e667…`; `implementation/refinements/fast_search_space_computation.v`; layer 21; rank 353.
- **8 public declarations:**
  - 2 definitions: `search_space_arrival_curve_prefix_FP_h` and `search_space_arrival_curve_prefix_FP`;
  - 6 `Prop` lemmas: `steps_lt_horizon_last_eq_horizon`, `structure_of_correct_search_space`,
    `multiple_of_horizon_in_approx_ss`, `steps_in_approx_ss`, `constant_max_arrivals` and
    `task_search_space_subset`.
- **Dependency (accepted):** `implementation/refinements/arrival_curve_prefix.v`.

## Translation

`Prosa/Implementation/Refinements/FastSearchSpaceComputation.lean` compiles with only the standard Lean axioms. Two
declarations use no axiom.

- **Representation** (as in `ArrivalCurve`):
  - `iota l r` is `List.range' l r`, `muln h` is `fun x => h * x`, and `predn` is `Nat.pred`;
  - `(L %/ h).+1` is `L / h + 1`, and `ε` is `1`;
  - `last0` is the accepted `Prosa.Util.List.last0` (`getLastD _ 0`);
  - `x \in xs` is `x ∈ xs`;
  - in `Prop` position, `a != b` is `decide (a ≠ b) = true` and `d %| m` is `decide (d ∣ m) = true`.
- **Binders:** the section's `L`, `ts`, `tsk` and hypotheses are explicit binders, in the order of the elaborated
  statements. Each statement takes only those it uses.
- **Proofs** follow the source, through the accepted extrapolated-arrival-curve facts
  (`extrapolated_arrival_curve_change`, `value_at_change_is_in_steps_of`,
  `sorted_ltn_steps_imply_sorted_leq_steps_steps`) and the accepted `arrival_curve_prefix` lemmas:
  - **`steps_lt_horizon_last_eq_horizon`:** strictly sorted time steps are bounded by the last one, which is at most
    the horizon.
  - **`structure_of_correct_search_space`:** a change of the extrapolated curve happens either at a multiple of the
    horizon, or at a step of the prefix. The quotient/remainder relations of `A` and `A + 1` are made explicit
    (`Nat.succ_div`).
  - **`constant_max_arrivals`:** when every step is below the horizon `h`, the value is constant on `[h - 1, h]`.
  - **Search-space membership:** a private lemma `mem_search_space`.
- **Private helpers:**
  - `le_last_of_sorted`, `last0_mem`, `steps_le_last0`, `valid_prefix`, `succ_div_cases`;
  - `div_mod_of_dvd_succ`: the arithmetic over plain `Nat`, so that `omega` is not blocked by the `duration`
    instances.
- **Local macro.** `omega'` is the accepted files' local macro (`omega` after unfolding `instant`/`duration`). It is
  a macro, not a declaration.

## Source binding

Source mode `official_closure`, with the run's CoqEAL build.
- **Closure:** `Validation/tooling/proof_closure/refinements_fast_search_space_computation_closure.txt`.
- **Patch:** `…-refinements-fast_search_space_computation.patch`.
  - It touches the 10 dependency files of the earlier refinements patches, plus `arrival_curve_prefix.v` (its
    recorded flag, as accepted), all proof-only.
  - It also adds `Set SsrOldRewriteGoalsOrder.` to the module.
- **Module change:** the spec opts in with `official_closure.module_change: "rewrite_goals_order_flag"`. It is
  checked line by line and recorded in the manifest.

### Type fingerprints

8/8 match the official-toolchain evidence:
- **7 `EXACT_MODULO_DEPENDENCY_MODULE_QUALIFIER`:** the `task.Task` qualifier, through the spec's
  `dependency_qualified_in_type`.
- **1 `EXACT_MODULO_DEPENDENCY_MODULE_QUALIFIER_AND_EXISTS_PARENS`:** `structure_of_correct_search_space`. Rocq
  9.0, which produced the official evidence, prints its final disjunct as `\/ (exists i : nat, …)`. Rocq 9.3 prints
  it as `\/ exists i : nat, …`.

### Pipeline addition (opt-in)

`translation_file_pipeline.py`: in the opt-in `dependency_qualified_in_type` branch, the repaired evidence may also
be normalized by exactly the accepted `TYPE_EQUAL_MODULO_EXISTS_PARENS` rule. That rule removes the parentheses
around a final `exists` operand of `\/`, `<->` or `~`. The result is recorded under its own status. Specs without the
field are unchanged.

## Validation

- **Spec:** `implementation_refinements_fast_search_space_computation.json`.
- **Lean base run:** `implementation_refinements_arrival_curve_prefix_final`.
- **Export:** 36,209 lines. Its root is:
  - the file's 2 definitions with bodies and its 6 statements statement-only;
  - the base refinements set;
  - the accepted task, arrival-curve and arrival-curve-prefix refinement definitions;
  - the concrete task and job definitions with their projections;
  - `Prosa.Util.List.last0`.

### Certificate chain (6 modules)

- **The 5 re-bound modules:** `RfsBase`, `RfsArrivalBound`, `RfsTask`, `RfsArrivalCurve` and
  `RfsArrivalCurvePrefix`. These are the accepted `refinements.v`, `arrival_bound.v`, `task.v`, `arrival_curve.v`
  and `arrival_curve_prefix.v` certificates, re-bound to this export without their statement correspondences.
- **Pruning.** They are pruned across the chain (`prune_chain.py`, see the `arrival_curve_prefix.v` report). The
  dropped commands are the same as there, plus `rf_head_ex` of `RfsArrivalCurvePrefix`, since `List.headD` is not in
  this export.
- **Every kept command is unchanged.**
- **`RefFastSearchSpaceComputationCorrespondence.v` (new, about 290 lines):**
  - **The two definitions** are related for related inputs: `map predn` with `List.map Nat.pred`, the offsets
    through the accepted `iota`/`muln` correspondences, and the bound `(L %/ h).+1`.
  - **Combinators** for `∧`, `∨` and `∃` over `nat`, and relations for:
    - equality of numbers;
    - `a != b` against `decide (a ≠ b) = true`;
    - membership in a related list;
    - MathComp `last0` against the accepted `last0`, by structural recursion.
  - **The six statements** are composed from these combinators, the implication and quantifier combinators of
    `arrival_curve_prefix.v`, and the accepted definition correspondences (`task_rbf`, `concrete_max_arrivals`,
    horizon, time steps, divisibility).
- **No certificate uses its own source or target theorem.** Statement types are taken with `type of`.
- **Audit:** 8 certificates.
  - 7 are `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` and 1 is `CERTIFIED`;
  - `semantic_premises=[]` and `unexpected=[]`;
  - no statement-only dependency;
  - no source or target theorem dependency;
  - `sorryAx` does not occur in the export.

### Attempts

- **Prepare attempt 1:** passed. `check` and `publish` also passed on their first runs.

## Formal acceptance

Coverage **349 / 357 files**, **2334 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
