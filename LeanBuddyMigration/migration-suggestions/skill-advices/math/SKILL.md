<span style="color:red"><strong>Purpose:</strong> Help when a rewrite theorem does not match the expression currently shown by the prover. Inspect both expressions, choose a useful common form, and establish a connecting equality when needed. After each rewrite, check the resulting goal to avoid cycling between equivalent forms.</span>

<span style="color:red"><strong>Proposed adaptation:</strong> Retain the proof method; replace MathComp identities and Coq templates with real Lean/Mathlib or RTS declarations. Do not require a MathComp iter stage in Lean or reuse Coq diagnostic mappings without Lean evidence. Original examples remain unchanged.</span>

---
name: coq-proof-state-discipline
#<span style="color:red"><strong>description recommendation:</strong> For a future Lean version, describe goal-driven rewriting across List/Finset/RTS expressions. Reason: MathComp rewrite names must not define Lean triggers.</span>
description: 'Debug Coq and ssreflect proofs by following the exact proof state, choosing rewrites only when their left-hand side literally matches the goal, and adding small bridge lemmas for bigop, iter, and multiplication mismatches. Use when rewrites fail, big_const_ord or big_distrr are involved, or a proof seems mathematically obvious but Coq reports that the lemma does not match any subterm.'
argument-hint: 'Describe the goal, the failed rewrite, and the current goal shape.'
user-invocable: true
---

# Coq Proof-State Discipline <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Choose rewrites from the actual proof state.</span>

<a id="lean-review-1"></a>

## When to Use <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Recognize expression mismatches and unstable normalization. | moderate adaptation</span>

<span style="color:red"><strong>Why:</strong> The named backend and bigop/iter representations are Coq-specific.<br><strong>Proposed change:</strong> Inspect the actual Lean List.sum, Finset.sum or RTS sum wrapper, preserving the goal-driven method.</span>

- A rewrite should work mathematically, but <span style="color:gray">Coq</span> rejects it.
- A proof oscillates between <span style="color:gray">`\sum_`, `iter`</span>, addition, and multiplication forms.

<span style="color:red"><strong>Why:</strong> The lemma names and diagnostic wording come from MathComp/Coq.<br><strong>Proposed change:</strong> Use actual Lean declarations such as Nat.one_mul and Nat.mul_comm, and observed Lean diagnostics.</span>

- <span style="color:gray">`mul1n`, `mulnC`, `big_ord_recr`, or `big_const_ord` fail with “does not match any subterm”</span>.
- You need a small bridge lemma between a local goal shape and the intended algebraic form.
- A large model is proposing steps from intuition instead of from the literal current goal.

<a id="lean-review-2"></a>

## Core Rule <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Inspect the current expression before choosing a rewrite.</span>
Choose the next lemma from the exact current goal syntax, not from mathematical intent alone.

If the left-hand side of the next lemma is not a literal subterm of the current goal, do not rewrite yet. First normalize one side or add a bridge lemma.

<a id="lean-review-3"></a>

## Procedure <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Check a rewrite and verify the resulting goal. | substantial adaptation</span>
1. Snapshot the exact goal.
   - Quote the full goal or the smallest relevant subterm.

   <span style="color:red"><strong>Why:</strong> The expression classification assumes MathComp big operators.<br><strong>Proposed change:</strong> Classify the real Lean expression: List.sum, Finset.sum, or Prosa.Util.Sum.sumSeq/sumFiltered.</span>

   - Record the head form: <span style="color:gray">`bigop`, `iter`, `addn`, `muln`, or boolean-as-nat</span>.
2. Name the intended rewrite.
   - Write the lemma you want to use.
   - Write its exact left-hand side.
3. Run the shape check.
   - Ask whether that left-hand side occurs syntactically in the current goal.
   
   - If the answer is no, stop and choose a bridge step instead.
4. Add the smallest bridge lemma that fixes the mismatch.
   - Prefer a local lemma when the mismatch is specific to a fixed variable, branch, or index.
   - Prefer a generic lemma only when the same mismatch recurs across proofs.
5. Normalize inside-out.
   - First settle constant or boolean-valued inner sums.
   - Then distribute or factor outer sums.

   <span style="color:red"><strong>Why:</strong> mulnC is the MathComp name for multiplication commutativity.<br><strong>Proposed change:</strong> Use Nat.mul_comm for Nat multiplication after checking the selected expression.</span>

   - Use arithmetic rewrites such as <span style="color:gray">`mulnC`</span> only after multiplication is literally present.
6. Validate after each nontrivial rewrite.
   - Re-read the new goal head form.

   <span style="color:red"><strong>Why:</strong> MathComp constant-sum normalization can expose iter; Lean need not use that intermediate form.<br><strong>Proposed change:</strong> Follow the actual Lean result, using constant-sum simplification rather than recreating an iter stage.</span>

   - <span style="color:gray">If the goal moved from `bigop` to `iter`</span>, update the plan before continuing.
7. Keep one stable normal form.

   <span style="color:red"><strong>Why:</strong> The strategy is reusable, but its example normal forms use MathComp syntax.<br><strong>Proposed change:</strong> Name the corresponding Lean sum, cardinality or multiplication form and keep it stable.</span>

   - Avoid oscillating between <span style="color:gray">`\sum_(i < n) x`, `iter n (addn x) 0`</span>, `x * n`, and `n * x` in the same branch.

## Bridge Lemma Strategy <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Choose a local or reusable connecting equality.</span>

<a id="lean-review-4"></a>

### Prefer a local bridge lemma when <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Use a local bridge for a context-specific conversion. | moderate adaptation</span>
- The expression depends on a fixed local variable such as `t`, `cpu`, or a branch condition.
- A boolean-valued term becomes a constant over an index.
- The proof only needs the lemma once.

Template:

<a id="lean-review-code-1"></a>

<span style="color:red"><strong>Purpose:</strong> Connect the original constant contribution sum to its numeric form.<br><strong>Proposed Lean adaptation:</strong> Use the actual RTS Classic declarations and explicit Bool.toNat where a Bool contributes a number. Replace MathComp sum notation and local-proof syntax.</span>

```coq
have cpu_sum_of_backlogged t :
  \sum_(cpu < num_cpus) (backlogged job_arrival job_cost sched j t) =
  backlogged job_arrival job_cost sched j t * num_cpus.
Proof.
  by case: (backlogged job_arrival job_cost sched j t);
     rewrite big_const_ord ?iter_addn ?mul1n ?mul0n ?addn0.
Qed.
```

<a id="lean-review-5"></a>

### Prefer a generic bridge lemma when <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Use a reusable bridge for a recurring identity. | moderate adaptation</span>
- The same normalization gap appears in multiple proofs.
- The goal has already become a literal constant sum.

Template:

<a id="lean-review-code-2"></a>

<span style="color:red"><strong>Purpose:</strong> Prove that a fixed number of identical summands equals their product.<br><strong>Proposed Lean adaptation:</strong> For the analogous Fin-indexed Nat sum, propose simp with Nat.mul_comm. Do not recreate the MathComp iter stage unless the actual Lean definition requires it.</span>

```coq
Lemma big_const_ord_muln n x :
  \sum_(i < n) x = x * n.
Proof.
  by rewrite big_const_ord iter_addn mulnC.
Qed.
```

<span style="color:red"><strong>Why:</strong> The referenced templates are Coq .v resources.<br><strong>Proposed change:</strong> A future Lean version would need Lean resources matching the actual API. Do not claim the original references are already translated.</span>

More ready-to-copy templates are in [bridge-lemma-templates](assets/bridge-lemma-templates.v).

<a id="lean-review-6"></a>

## Bigop Endgame Discipline <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Keep the final sum and arithmetic form stable. | substantial adaptation</span>

<span style="color:red"><strong>Why:</strong> The endgame rules refer to SSReflect/MathComp rewrites.<br><strong>Proposed change:</strong> Use actual List/Finset sum identities and Lean rw/simp while preserving the chosen normal form.</span>

<span style="color:gray">For ssreflect big operator proofs</span>, use this order.

1. Exchange or rearrange sums only while the goal is still clearly a big operator.
2. Collapse branch-local constant sums.

<span style="color:red"><strong>Why:</strong> The expression mixes a Bool contribution with MathComp sums.<br><strong>Proposed change:</strong> Make Bool.toNat explicit where needed. RTS sumSeq and sumFiltered use List map/sum; preserve their list semantics.</span>

3. <span style="color:gray">Introduce local bridge lemmas for boolean-as-nat constants</span>.

<span style="color:red"><strong>Why:</strong> big_distrr is a MathComp distributivity lemma.<br><strong>Proposed change:</strong> Choose Finset.sum_mul or Finset.mul_sum for the actual multiplication side; inspect direction before rewriting.</span>

4. Use <span style="color:gray">`big_distrr`</span> or similar outer distribution only after inner normalization is stable.

<span style="color:red"><strong>Why:</strong> mulnC is a MathComp identifier.<br><strong>Proposed change:</strong> Use Nat.mul_comm for Nat expressions, only at the intended multiplication subterm.</span>

5. Use algebraic rewrites such as <span style="color:gray">`mulnC`</span> only when multiplication is literally present.

<a id="lean-review-7"></a>

## When To Switch To Count Bridging <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Route counting-representation problems to count-bridging. | moderate adaptation</span>

<span style="color:red"><strong>Why:</strong> The iter checkpoint reflects a MathComp implementation choice.<br><strong>Proposed change:</strong> Choose the next step from the actual Lean expression instead of requiring an iter phase.</span>

This skill handles generic big-operator, <span style="color:gray">`iter`</span>, and multiplication mismatches.

<span style="color:red"><strong>Why:</strong> The destination skill currently includes a MathComp Bool-reflection workflow.<br><strong>Proposed change:</strong> Keep routing for counting representations, but propose removal of its fixed Bool/Prop roundtrip subsection.</span>

If the branch has clearly become a counting proof, switch to [ssreflect-count-bridging](skill_count.md) instead of staying here.

High-signal cues for switching:

<span style="color:red"><strong>Why:</strong> The routing cues use old library names.<br><strong>Proposed change:</strong> Recognize Lean indicator sums, List.countP/filter and Finset.sum/card instead.</span>

- <span style="color:gray">the branch mixes `big_mkcond`, `sum1_count`, `big_filter`, `count`, and `Nat.min` or `minn`</span>
- the same quantity appears both as `if P x then 1 else 0` and as a <span style="color:gray">`count`</span>
- the endgame is no longer a pure big-operator identity, but a bound on how many elements satisfy a predicate

<span style="color:red"><strong>Why:</strong> The distinction remains valid, but count and bigop name old interfaces.<br><strong>Proposed change:</strong> Route countP/card conversions to count-bridging; keep general sum equalities here.</span>

- the next intended theorem lives in the <span style="color:gray">`count`</span> or `min` layer rather than in the generic <span style="color:gray">`bigop` or `iter`</span> layer

Use this generic skill only up to the point where the proof class is clear. Once the branch is really about indicator-sum to count normalization, the count-bridging skill has the stricter pipeline.

<a id="lean-review-8"></a>

## Side-Specific Normalization <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Normalize only the side that needs changing.</span>
Sometimes the cleanest fix is to rewrite only one side into the other side’s syntax.

Example:

<a id="lean-review-code-3"></a>

<span style="color:red"><strong>Purpose:</strong> Rewrite only the right side back into a useful sum form.<br><strong>Proposed Lean adaptation:</strong> Use a proved Lean sum equality in reverse within the intended side, for example conv followed by rhs and rw. Preserve the chosen normal form on the other side.</span>

```coq
rewrite [in RHS]-big_const_ord.
```

<span style="color:red"><strong>Why:</strong> This reverse normalization uses a MathComp iter/bigop relationship.<br><strong>Proposed change:</strong> In Lean, use a proved sum equality in the required direction and scope, for example a right-hand-side conv block. Do not require iter.</span>

Use this when the goal is naturally a big operator and <span style="color:gray">forcing the other side into multiplication would create an unstable `iter` intermediate</span>.

<a id="lean-review-9"></a>

## Common Failure Signatures <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Relate historical rewrite failures to checks. | substantial adaptation</span>
See [failure-signatures](references/failure-signatures.md) for a mapping from common error messages to the missing normalization step.

Short version:

<span style="color:red"><strong>Why:</strong> This diagnostic is a Coq-specific signature.<br><strong>Proposed change:</strong> Use an observed Lean diagnostic with its current goal and attempted rewrite; do not copy the old cause mapping.</span>

- <span style="color:gray">`Unable to unify "X * n" with "iter n (addn X) 0"` means the goal is still in `iter` form</span>.

<span style="color:red"><strong>Why:</strong> The error names a MathComp lemma and its matching behavior.<br><strong>Proposed change:</strong> Rebuild the entry from the actual Lean rewrite and source position.</span>

- <span style="color:gray">`The LHS of mul1n ... does not match any subterm`</span> means there is no literal `1 * _` yet.
- <span style="color:gray">`The LHS of mulnC ... does not match any subterm`</span> means there is no multiplication node yet, or not the one you think.

<span style="color:red"><strong>Why:</strong> The message depends on the old sum/iter representation.<br><strong>Proposed change:</strong> Inspect the actual Lean sum or multiplication state before recommending normalization.</span>

- <span style="color:gray">`The LHS of big_ord_recr ... does not match any subterm` means the goal is no longer a standard ordinal big operator head</span>.

<span style="color:red"><strong>Why:</strong> This Coq message does not establish a corresponding Lean cause.<br><strong>Proposed change:</strong> Defer a Lean signature until a reproducible Lean case supports the diagnosis.</span>

- <span style="color:gray">`No applicable tactic`</span> after several rewrites usually means the proof drifted across multiple normal forms without a stable bridge.

<span style="color:red"><strong>Why:</strong> The routing examples use MathComp count/bigop names.<br><strong>Proposed change:</strong> Use the corresponding Lean counting forms when selecting count-bridging.</span>

<span style="color:gray">If the branch now mentions `big_mkcond`, `sum1_count`, filtered sums of ones, or `count` bounds</span>, stop here and switch to [ssreflect-count-bridging](skill_count.md). That is no longer a generic bigop mismatch; it is a counting-normalization proof.

<a id="lean-review-10"></a>

## Anti-Patterns <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Avoid blind rewrites and representation oscillation. | moderate adaptation</span>

- Do not rewrite because two expressions are mathematically equal if the target lemma does not literally match the goal.

<span style="color:red"><strong>Why:</strong> This chain consists of MathComp lemma names.<br><strong>Proposed change:</strong> Use verified Lean identities and inspect the result after each normalization step; retain the warning against blind rewrite chains.</span>

- Do not chain <span style="color:gray">`big_const_ord`, `iter_addn`, `mul1n`, and `mulnC`</span> blindly without checking the intermediate goal.
- Do not use a generic arithmetic lemma when a branch-local bridge lemma is simpler and more robust.
- Do not switch normal forms repeatedly inside one proof branch.

<a id="lean-review-11"></a>

## Minimal Debug Log <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Record the current expression, proposed equality and result.</span>
Keep a short log while debugging.

```text
Current goal subterm:
Desired lemma:
Lemma left-hand side:
Literal match in goal: yes/no
If no, bridge lemma or normalization step:
Resulting goal head form:
```

<a id="lean-review-12"></a>

## Success Condition <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Confirm that the goal has reached the required form.</span>

The proof is on track when each rewrite is justified by a literal syntactic match, and every bridge lemma moves the branch toward a single stable normal form instead of introducing another oscillation.
