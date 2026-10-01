# implementation/refinements/arrival_curve_prefix.v — canonical translation report

First experiment timestamp: **2026-10-07 14:00:00 +08:00**

The fifth file behind the CoqEAL build boundary. It uses the same local CoqEAL 2.1.2 build and official-toolchain
type evidence as `refinements.v`. That report covers CoqEAL's provenance and how the evidence was produced.

## Authority and scope

- Prosa v0.6 `414e667…`; `implementation/refinements/arrival_curve_prefix.v`; layer 20; rank 352.
- **4 public `Prop` lemmas:**
  - `has_valid_arrival_curve_prefix_tsk`;
  - `steps_are_positive_if_first_step_is_positive`;
  - `nonshifted_offsets_are_positive`;
  - `time_steps_sorted`.

  They are stated for a task set with valid arrivals and a task of it, with the section's hypotheses as premises,
  in the order of the elaborated types.
- **Dependency (accepted):** `implementation/refinements/arrival_curve.v`.
- **Acceptance order:** this file is accepted before ranks 348–351 (the four EDF/FP `*_sched.v` files). Those files
  need a separate certificate adapter for schedules over the concrete job type (see Validation). The rank order has
  no other effect.

## Translation

`Prosa/Implementation/Refinements/ArrivalCurvePrefix.lean` compiles with only the standard Lean axioms. All four
theorems use `propext` and `Quot.sound`.

- **Representation** (as in `ArrivalCurve`):
  - `head (0, 0) s` is `s.headD (0, 0)`;
  - `sorted ltn s` is the accepted `sortedBool` with `decide (· < ·)`;
  - `x \in xs` is `x ∈ xs`.
- **Proofs** follow the source:
  - **Valid prefix.** Do a case analysis on the arrival bound. For a periodic or sporadic task, the
    inter-arrival prefix `(p, [(1, 1)])` is valid. For an arrival-curve prefix, validity comes from the accepted
    reflection `valid_arrival_curve_prefix_P`.
  - **Positive and ordered time steps.** Strict ordering of the steps makes every time step at least the first
    one. A private lemma maps the strict step order to the time steps.
  - **Positive offsets** follow from positive steps.

## Source binding

Source mode `official_closure`, with the run's CoqEAL build.
- **Closure:** `Validation/tooling/proof_closure/refinements_arrival_curve_prefix_closure.txt`.
- **Patch:** `Validation/patches/prosa-v06-rocq93-official-proof-closure-refinements-arrival_curve_prefix.patch`. It
  touches the same 10 dependency files as the earlier refinements patches, all proof-only. It also adds
  `Set SsrOldRewriteGoalsOrder.` after the imports of the module itself, since its official proofs need the Rocq 9.0
  rewrite-goal order.
- **Module change:** the spec opts in with `official_closure.module_change: "rewrite_goals_order_flag"`, the rule
  introduced for `arrival_bound.v`. The pipeline checks line by line that the compiled module is the official file
  plus exactly that one line, and records it in the manifest.

### Type fingerprints

4/4 match the official-toolchain evidence, all `EXACT_MODULO_DEPENDENCY_MODULE_QUALIFIER`.
- The official evidence prints `seq task.Task` and `task.Task`. The validation context prints `Task`, which
  denotes the same `task.v` declaration.
- The spec lists `dependency_qualified_in_type: ["prosa.implementation.refinements.task.Task"]`. That rule was
  introduced for `arrival_curve.v` and is used here unchanged.

## Validation

- **Spec:** `implementation_refinements_arrival_curve_prefix.json`.
- **Lean base run:** `implementation_refinements_arrival_curve_final`.
- **Export:** 35,873 lines. Its root is the 4 statements statement-only, plus:
  - the base refinements set;
  - the accepted arrival-bound, task and arrival-curve refinement definitions;
  - the concrete task and job definitions with their projections.

### Certificate chain (5 modules)

- **`RacpBase`, `RacpArrivalBound`, `RacpTask`, `RacpArrivalCurve`:** the accepted `refinements.v`,
  `arrival_bound.v`, `task.v` and `arrival_curve.v` certificates, re-bound to this export without their statement
  correspondences.
- **What was dropped.** This file has no `Type`-valued statement, so the export lacks `PLift.down` and a few list
  constants. The commands that mention them are dropped, together with every command (in any later module of the
  chain) that uses a dropped one:
  - `RacpBase`: `rf_min_ex`, `rf_max_ex`, `rf_size_ex`, `rf_iota_ex`, `rf_zip_ex`, `rf_sumSeq_ex`,
    `rf_sumFiltered_ex`, `rf_maxFiltered_ex`, `rnat_bw`, `rnat_bw'`, `rf_corr_11`, `rf_corr_21`, `rf_corr_2b`,
    `lrnat_bw`, `lrnat_bw'`, `rf_corr_lsl`, `prr_bw`;
  - `RacpArrivalBound`: `RArrivalCurvePrefix_correspondence`, `Rtask_ab_correspondence`, `pfxR_bw`,
    `rf_corr_pp2b`, `rf_corr_sorted`, `rf_corr_p11`, `rtab_bw`, `rtab_fw`;
  - `RacpTask`: `Rtask_correspondence`, `rtask_fw`, `rtask_bw`, `rf_corr_tf`, `rf_corr_tn`, `rtab_bw'`,
    `rf_corr_nab`;
  - `RacpArrivalCurve`: `rf_corr_t2`.
- **Every kept command is unchanged.**
- **`RefArrivalCurvePrefixCorrespondence.v` (new, about 170 lines):**
  - **Combinators.** Generic `PropSPropRel` combinators for implication and universal quantification. The
    quantifiers range over tasks, task lists, numbers and number lists, and are covered in both directions by the
    canonical maps and their roundtrips.
  - **Components:**
    - the canonical `nat` order;
    - the head of the steps, through `get_arrival_curve_prefix`;
    - strict sortedness, through the accepted `rf_sorted_ex`;
    - membership in tasks and numbers, through the generic membership correspondence of the `arrival_curve.v`
      certificate;
    - the accepted definition correspondences of `arrival_curve.v`: `task_set_with_valid_arrivals`,
      `has_valid_arrival_curve_prefix`, `get_time_steps_of_task` and `repeat_steps_with_offset`.
  - **The four statements** are composed from these.
- **No certificate uses its own source or target theorem.** Statement types are taken with `type of`.
- **Audit:** 4 certificates, all `CERTIFIED_WITH_PROP_SPROP_FOUNDATION`.
  - `semantic_premises=[]` and `unexpected=[]`;
  - no statement-only dependency;
  - no source or target theorem dependency;
  - `sorryAx` does not occur in the export.

### Tooling (scratch, not part of the pipeline)

`prune_chain.py` is `prune_base.py` over a whole re-bound chain. It carries the names dropped in one module into the
later modules, so that a kept command never refers to a dropped one. It changes no kept command.

### Attempts

- **Attempt 1:** archived as `_attempt1_module_flag_not_declared`. The closure patch adds the rewrite-order flag to
  the module, but the spec had not declared `module_change`, so the pipeline refused the patched module, as
  designed.
- **Attempt 2:** passed prepare, then `check` and `publish`.

## Formal acceptance

Coverage **348 / 357 files**, **2326 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
