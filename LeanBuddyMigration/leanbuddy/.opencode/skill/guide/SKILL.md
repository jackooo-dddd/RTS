---
name: lean-proof-methodology
description: Use for general Lean 4 proof development and recovery when the blocker is a goal-state, tactic, typing, focusing, rewrite, or incomplete-proof issue and no narrower skill already explains it.
---

# Lean Proof Methodology

Use this skill as a compact recovery loop, not as a second copy of the agent's proof policy. Prefer a narrower skill when the diagnostic already identifies a specific pattern such as goal focus (`goal-focus-discipline`), a failed lemma application (`lean-goal-driven-apply`), a rewrite that does not match (`lean-rewrite-discipline`), or count/sum bridging (`lean-count-bridging`).

## Core loop

1. Read the exact current goals and local context (`lean_session` goal state, or the `unsolved goals` message).
2. Fix the first reliable error only: syntax and indentation, then typing/elaboration, then tactic failure or unsolved goals.
3. Make one small proof-producing step or edit.
4. Re-run the smallest relevant check (`lean_session` step, then `lean_check`/`checkpoint` on the staged file).
5. Persist a validated step in the proof file, or undo only its failing tail.

Do not respond to a failed step with an unrelated broad search. A targeted lookup (`lean_query #check @name`, `search`, `lsp` hover) is justified when the current goal or error names the missing definition, lemma shape, instance, or premise; use its result in the next proof attempt.

## Scope and proof integrity

- Keep edits inside the currently owned theorem or proof_region.
- Preserve compiler-certified prefixes and the current transaction state.
- Do not introduce `axiom`, new `variable`s or hypotheses, `admit`, `native_decide`, or options that skip checking as a proof substitute. A `sorry` in an authorized skeleton region is a placeholder, not success.
- Do not change theorem statements or declarations to make the proof easier.
- A benchmark proof is finished only when no `sorry` remains and the final checkpoint (frozen statement, `lake build`, `#print axioms`) passes.

## Goal and branch discipline

- Inspect the goals after a tactic that rewrites, applies a lemma, introduces a local fact, or splits.
- Use `·` (or `case tag =>`, `next =>`) to focus one goal at a time; repair focusing and indentation before changing semantic tactics.
- When a one-line tactic chain (`tac1 <;> tac2`, a long `simp [...]`, `by exact …` inside a term) hides the failure, unfold it into separate lines and inspect the first revealed goal.
- For a dependent rewrite (`motive is not type correct`), consider `subst` for a variable equality, `simp only`, `conv`, or a `calc` step; or `generalize`/`revert` the dependent hypotheses first.

## Choosing the next step

Choose tactics from the actual goal shape; this is guidance, not a mandatory route:

- definitional equality: `rfl`, `show …` with the unfolded form, `unfold`/`simp only [f]`;
- available hypothesis or constructor: `exact`, `assumption`, `apply`, `refine ⟨_, _⟩`, `constructor`, `left`, `right`, `exists`;
- equality transport: `rw [h]`, `subst`, `congr`/`congrArg`, `calc`;
- local bridge: `have h : P := by …`, `obtain ⟨x, hx⟩ := …`, `suffices h : P by …`, `set x := … with hx`;
- arithmetic: `omega` (ℕ/ℤ linear), `linarith`/`nlinarith` (ordered fields and ℕ after casting), `norm_num`, `ring`, `positivity`;
- bounded search: `simp`, `aesop`, `tauto` only on goals whose shape you have checked; prefer `simp only [...]` with the lemmas you mean in long proofs.

## Candidate lemma audit

Before committing to an imported lemma:

1. inspect its exact type (`#check @name`), including implicit and instance arguments;
2. unify its conclusion with the live target (try it in `lean_session`: `apply name` or `refine name ?_ ?_`);
3. list the remaining goals it produces and the implicit arguments Lean could not infer;
4. check whether each premise follows from current hypotheses or an already certified local bridge;
5. abandon or change the instantiation when a required premise is unavailable.

A verified failed lemma/missing-premise route must not be repeated through cosmetic edits or an `admit_id` rename. It may be reconsidered after a new hypothesis is derived, the missing premise is checked, the instantiation genuinely changes, or the audit is shown wrong.

## Completion check

Before reporting success, verify:

- the current owned goal is closed (`lean_session` reports no goals for it);
- no `sorry` remains in the owned theorem or region;
- the authoritative staged revision, not an older disk copy, passes `checkpoint`/`lean_check`;
- all opened branches and local `have`s are closed;
- for the whole theorem, the final checkpoint passed the final gate.

If the proof still fails, return the exact stable goal/error, the smallest failed step, missing premises, and which certified prefix remains reusable.
