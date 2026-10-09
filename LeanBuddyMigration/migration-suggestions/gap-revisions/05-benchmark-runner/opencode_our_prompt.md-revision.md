# Revision: `scripts/scripts_junyi/opencode_our_prompt.md` (task prompt template)

**File**: [`opencode_our_prompt.md`](../../../prosabuddy-rocq/scripts/scripts_junyi/opencode_our_prompt.md) (100 lines). **Rename to** `lean_task_prompt.md`.
**Change size**: Rewrite of the objective and file sections. **Follows**: DECISIONS D2, D4.

| Part | Current | Lean version |
|---|---|---|
| Title / role (L1-L3) | "Coq Theorem-Proving Benchmark … Coq theorem-proving agent" | "Lean Theorem-Proving Benchmark … Lean 4 theorem-proving agent". |
| Objective (L5-L10) | "Complete the proof in the designated working `.v` file … ends with `Qed.` and compiles with `coqc`" | "Replace the `sorry` in `Solution.lean`; the run succeeds only when the final gate passes (frozen `Statement.lean`, no forbidden tokens, `lake build`, the statement check and `#print axioms`)". |
| Read scope (L12-…) | "the single target `.v` file", staged Prosa `.v` files | "`Solution.lean` (editable), `Statement.lean` and `proof.tex` (read-only), `Prosa/` and Mathlib (read-only); helper modules may be created under `CaseStudies/`". |
| Remaining Coq wording (15 occurrences) | `coqc`, `.v`, `Admitted`, `Qed`, SSReflect | replace per DECISIONS D2/D4; no Rocq tool names (D2 rule). |
