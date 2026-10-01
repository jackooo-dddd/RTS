# results/rta/ideal/fp/comp/fully_preemptive.v — canonical translation report

First experiment timestamp: **2026-10-06 21:00:00 +08:00**

## Authority and scope

- Prosa v0.6 `414e667…`; `results/rta/ideal/fp/comp/fully_preemptive.v`; layer 28; no dependents.
- Public declarations: **1**, the statement `uniprocessor_response_time_bound_fully_preemptive_fp`.
  - This is the fully preemptive FP bound with `L` and `R` computed by the `util/fixpoint` searches: `L` by
    `find_fixpoint` of the total higher-or-equal-priority RBF, and `R` by `find_max_fixpoint` over the FP search space.
- Dependencies (all accepted): `results/rta/ideal/fp/fully_preemptive.v`, `util/fixpoint.v`.

## Translation

`Prosa/Results/Rta/Ideal/Fp/Comp/FullyPreemptive.lean`; it compiles with only the standard Lean axioms.

- **Binders:** follow the elaborated type.
- **Section-local instances:** the readiness (the accepted `sequential_ready_instance` at the arrival sequence) and
  the accepted `fully_preemptive_job_model` are passed explicitly where the elaborated statement uses them
  implicitly.
- **The search space and the recurrence:**
  - the section-local `is_in_search_space` is the accepted ideal FP `bounded_pi` definition at `tsk` and `L`;
  - `recurrence` is inlined.
- **Representation:** `Some` is `some`, a Boolean in `Prop` position is `= true`, `x \in xs` is
  `decide (x ∈ xs) = true`, and `ε` is `1`.

The proof follows the source:
- **Pathological case:** if the total higher-or-equal-priority RBF at `1` is `0`, the accepted
  `pathological_total_hep_rbf_any_bound` applies.
- **Otherwise:**
  - the accepted fixpoint facts give `0 < L` and `L = total_hep_rbf L` (`ffp_finds_positive_fixpoint`, with the
    accepted RBF monotonicity, and `ffp_finds_fixpoint`);
  - `fmf_is_maximum` and `ffp_finds_fixpoint` give, for each `A` in the search space, a solution `F ≤ R` of the
    recurrence;
  - the accepted ideal FP fully preemptive theorem then applies.

## Source binding

Extract mode, module `RtaIdealFpCompFullyPreemptiveSemanticSource`. Fingerprint:
`STATEMENT_BODY_EQUAL_TO_ELABORATED_TYPE`.

Bindings:
- **Base closure:** the accepted ideal FP `fully_preemptive` run.
- **The official `util/fixpoint.v`:** pinned, with `util/minmax.v` (and `util/setoid.v`) compiled in the source tree.
  The statement uses the official `find_fixpoint` and `find_max_fixpoint`.
- **Two new proof-only Rocq 9.3 compatibility patches** (`extra_source_patches`, re-applied and hash-checked at
  finalization):
  - `patches/prosa-v06-rocq93-util-minmax.patch`;
  - `patches/prosa-v06-rocq93-util-fixpoint.patch`.
- **Why the patches are needed:**
  - **Root cause.** Under `rocq93rc1` the ssreflect `done` is `Corelib.ssr.ssreflect_rw.done`. The accepted
    `util/tactics.v` compatibility patch writes the reference as a bare `done`. Inside
    `Ltac done := solve [ done | … ]` that name refers to Prosa's `done` itself, so `by` / `//` closers can recurse
    until `Stack overflow` (first at `util/minmax.v` line 12).
  - **Why `util/tactics.v` is not changed.** Accepted `.vo` hashes depend on it.
  - **The fix in both patches.** Each adds one file-local line that restores the original definition for that file
    only: `Local Ltac done := solve [ Corelib.ssr.ssreflect_rw.done | eauto 4 with basic_rt_facts ].`
  - **`util/fixpoint.v` also inlines** the two-line proof of the `util/list.v` lemma `has_all_nilp` at its only use
    (in the proof of `fmfs_finds_fixpoint`). The validation closure binds `util/list.v` by its accepted
    statement-only semantic source.
  - **No statement or definition is changed.**
- **Lean closure:**
  - `Prosa/Util/Fixpoint.olean` is rebuilt by the pipeline (`extra_lean`); the rebuilt olean equals the hash
    recorded in the accepted `util_fixpoint` manifest;
  - the accepted `FixpointComputationInterface` root was added;
  - its 33 equations are exported as body theorems, and the four fixpoint-search definitions as definition targets.

## Validation

- **Spec** `results_rta_ideal_fp_comp_fully_preemptive.json`; base run `results_rta_ideal_fp_fully_preemptive`.
- **Export:** 160,376 lines.

Certificate chain (56 modules):
- **The accepted ideal replay chain**, with `IdlStateRel` and these replayed modules:
  - `PreemptionTimeCorrespondence` and `NatSubCorrespondence`;
  - the accepted `util/fixpoint` certificates `FixpointBaseCorrespondence`, `FixpointMonotoneCorrespondence` and
    `FixpointMaxOperations`.
- **Retargeting the fixpoint certificates:**
  - they were retargeted from the accepted `ImportedFixpoint` and the extracted `GeneratedFixpointSource(All)` to
    this export and the official `prosa.util.fixpoint`;
  - their `Print Assumptions` lines were removed; the audit module prints the assumptions of the correspondences
    used;
  - all 78 imported constants they use have identical signatures in this export, so no constant was renamed;
  - every replayed module compiled with no block dropped.
- **`RtaIdealFpCompFullyPreemptiveCorrespondence.v`:**
  - **Helper part:** the accepted ideal helper part, with the same dropped blocks as the accepted ideal FP
    `fully_preemptive` certificate. They name the two ideal interference instances or an `iw_instantiation`
    statement constant, none of which this export contains, and they are not used.
  - **As in the accepted ideal FP `fully_preemptive` certificate:** the FP-policy layer, the task-set predicates, the
    FP policy at preemption points, the concrete FP search space, sequential readiness and the fully preemptive
    model.
  - **The two fixpoint hypotheses:**
    - `find_fixpoint`, by the accepted `fixpoint_some_eq_correspondence`, at the accepted
      `total_hep_request_bound_function_FP` relation;
    - `find_max_fixpoint`, by the accepted `fixpoint_max_wrapper_some_eq_correspondence`, at the search-space
      predicate and the recurrence (addition and subtraction by the accepted relations);
    - each with an equality-symmetry step, since the statement writes `Some L = …`.
  - **The one correspondence.**

No source or target theorem is used.

Attempts:
- **Prepare:** attempt 1 passed.
- **First replay:** it stopped because `FixpointMonotoneCorrespondence` imports `NatSubCorrespondence`, which was not
  yet in the replay list. It was added, and the replay passed with no block dropped.
- **Template:** compiled on the first attempt.
- **Finalization:** attempt 1 was accepted.

Audit: 16 certificates, 12 `CERTIFIED_WITH_PROP_SPROP_FOUNDATION` and 4 `CERTIFIED`:
- `semantic_premises=[]`, `unexpected=[]` and no statement-only dependency;
- `sorryAx` does not occur in the export.

## Formal acceptance

Coverage **340 / 357 files**, **2175 / 2439 declarations**. Status: **ACCEPTED_V06_FILE**.
