<span style="color:red"><strong>Purpose:</strong> Help when a theorem and the goal express the same count differently. For example, four tasks contribute 1, 0, 1, 0 to a sum, while another theorem counts the two unfinished tasks directly. This skill connects those expressions, chooses the form expected by the theorem, and only then proves the bound.</span>

<span style="color:red"><strong>Proposed removal:</strong> <a href="#lean-review-bool-prop">Bool / Prop Separation through Boundary Failure Signs</a>. MathComp natural-number comparisons use Bool reflection; ordinary Lean Nat comparisons are already propositions. The fixed Bool-to-Prop-to-Bool arithmetic handoff is unnecessary. Remove that subsection in a future Lean version, while preserving genuine Bool-valued business definitions. The counting methodology remains useful.</span>

<span style="color:red"><strong>Proposed adaptation:</strong> <a href="#lean-review-normal-form">Normal-Form Decision</a> and <a href="#lean-review-template-1">Bridge Templates</a> should connect real Lean List/Finset representations. Preserve list multiplicities. All original text and examples below remain unchanged; these are review recommendations only.</span>

---
name: ssreflect-count-bridging
#<span style="color:red"><strong>description recommendation:</strong> For a future Lean version, describe bridging indicator sums, filtered counts and bounds using actual List/Finset representations. Reason: MathComp lemma names are not Lean trigger words.</span>
description: 'Handle ssreflect and MathComp proof branches where the same quantity appears as an indicator sum, a filtered big operator, a count, and then a min-bound or arithmetic inequality. Use when `big_mkcond`, `sum1_count`, `big_filter`, `count`, `Nat.min` or `minn`, or `if ... then 1 else 0` appear together and rewrites keep failing because the branch has no stable counting normal form.'
argument-hint: 'Describe the current indicator or count shape, the target equality or inequality, and the first failed rewrite or bridge step.'
user-invocable: true
---

# Ssreflect Count Bridging <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Connect equivalent ways of counting before proving a bound.</span>

## When to Use <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Recognize counting proofs that need a representation bridge. | moderate adaptation</span>

<span style="color:red"><strong>Why:</strong> MathComp notation and lemma names do not identify the corresponding Lean expressions.<br><strong>Proposed change:</strong> Use List.countP and List.sum for lists, or filtered Finset.card and Finset.sum for finite sets; replace minn with Nat.min. Preserve list duplicates.</span>

- A branch mixes <span style="color:gray">`\sum_`, `big_filter`, `big_mkcond`, `sum1_count`, `count`</span>, and `Nat.min` or <span style="color:gray">`minn`</span>.
- The current term is an indicator sum such as `if P x then 1 else 0`, but the intended lemma is about <span style="color:gray">`count`</span>.
- The proof is trying to bound how many elements satisfy a predicate and then feed that bound into a strict inequality or a `min` bound.
- The same quantity is being rewritten back and forth as a filtered sequence, a filtered big operator, and a raw count.
- A large model keeps proposing arithmetic or transitivity steps before the counting shape is stable.

## Core Rule <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Choose one counting form before doing arithmetic. | minor adaptation</span>
For this proof class, choose one counting normal form and move toward it monotonically.

Do not jump directly from an indicator sum to a `min` inequality or a final arithmetic step. First normalize the branch into one stable representation, usually:

1. indicator sum
2. filtered big operator
3. count
4. arithmetic or `min` bound

<span style="color:red"><strong>Why:</strong> The target representation still matters, but count and bigop are library-specific.<br><strong>Proposed change:</strong> Choose Lean countP/card or sum according to the next theorem. Keep the normalization strategy.</span>

If the next theorem is a theorem about <span style="color:gray">`count`</span>, normalize to <span style="color:gray">`count`</span> first. If the next theorem is a theorem about big operators, stay in filtered big-operator form. Do not oscillate between both.

## High-Signal Surface Cues <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Recognize expressions suggesting a counting mismatch. | moderate adaptation</span>
This skill is likely the right one if the failing branch contains several of these at once:

<span style="color:red"><strong>Why:</strong> These trigger names belong to MathComp.<br><strong>Proposed change:</strong> Use Lean indicator sums, List.countP/filter, Finset.filter/card, and the real bridges List.countP_eq_length_filter, Finset.sum_filter and Finset.sum_boole.</span>

- <span style="color:gray">`big_mkcond`</span>
- <span style="color:gray">`sum1_count`</span>
- <span style="color:gray">`big_filter`</span>
- <span style="color:gray">`count`</span>
- <span style="color:gray">`filter`</span>
- `Nat.min` or <span style="color:gray">`minn`</span>
- `if P x then 1 else 0`
- local names like `count_exceeding`, `other_tasks`, `rest_tasks`, or similar “count selected elements of a remainder list” helper facts

One cue alone is not enough. The class appears when the same quantity is drifting across these different shapes.

<a id="lean-review-normal-form"></a>

## Normal-Form Decision <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Choose a count or a sum to match the next theorem. | moderate adaptation</span>
Before rewriting, answer this first:

- Is the endgame a count theorem, a cardinality theorem, or an arithmetic inequality about how many elements satisfy a predicate?
- Or is the endgame still a big-operator identity?

If the endgame is about how many elements satisfy a predicate, prefer this target normal form:

<span style="color:red"><strong>Why:</strong> MathComp count counts occurrences in a sequence; Finset.card counts distinct elements.<br><strong>Proposed change:</strong> Use <code>s.countP P</code> for a Bool predicate on a list, or <code>(s.filter P).card</code> for a decidable proposition on an existing Finset. Do not deduplicate a list.</span>

```text
count P s
```

If the endgame is still a summation theorem, prefer this target normal form:

<span style="color:red"><strong>Why:</strong> This is MathComp filtered-sum notation.<br><strong>Proposed change:</strong> Use a filtered List followed by map/sum, or a sum over a filtered Finset. Keep the original indexing and value type.</span>

```text
\sum_(x <- s | P x) 1
```

Once chosen, keep the whole branch moving toward that form only.

<a id="lean-review-procedure"></a>

## Required Procedure <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Inspect the expression, establish its bridge, then prove the bound. | moderate adaptation</span>
1. Freeze the branch and name the current shape.
   - indicator sum
   - filtered big operator
   - count
   - `min` or arithmetic layer
2. Decide the target normal form.

   <span style="color:red"><strong>Why:</strong> The count interface changes with the library.<br><strong>Proposed change:</strong> Target List.countP or filtered Finset.card; retain a sum if the next theorem expects a sum.</span>

   - If the next useful fact is about <span style="color:gray">`count`</span>, normalize toward <span style="color:gray">`count`</span>.
   - If the next useful fact is about big operators, normalize toward filtered big operators.
3. If the branch still contains `if P x then 1 else 0`, remove the indicator encoding first.

   <span style="color:red"><strong>Why:</strong> big_mkcond is a MathComp bridge.<br><strong>Proposed change:</strong> For Finset, use Finset.sum_filter; for List, use a matching lemma or a local proof by list induction and predicate cases.</span>

   - Use <span style="color:gray">`big_mkcond`</span> or an equivalent bridge step to expose the predicate as a filter condition.
4. If the branch is now a filtered sum of ones, collapse it to a count.

   <span style="color:red"><strong>Why:</strong> sum1_count is not the Lean interface.<br><strong>Proposed change:</strong> Use List.countP_eq_length_filter with simplification, or simplify a Finset sum of ones to its cardinality.</span>

   - Use <span style="color:gray">`sum1_count`</span> or an equivalent local bridge fact.
5. Only after the count shape is stable should you apply list-splitting, subset, or `min` lemmas.
6. Only after the count bound is stable should you perform the final arithmetic step.
   <span style="color:red"><strong>Why:</strong> Ordinary Lean Nat comparisons are already Prop.<br><strong>Proposed change:</strong> Remove this fixed handoff requirement along with the reflection subsection; handle Bool only when an actual business definition returns Bool.</span>

   - <span style="color:gray">Keep boolean comparisons and Prop arithmetic separate until you explicitly bridge them.</span>
7. If the branch needs a local connector fact, name it and keep it local.

   <span style="color:red"><strong>Why:</strong> The SSReflect anonymous have-rewrite syntax does not carry over.<br><strong>Proposed change:</strong> Propose a named <code>have hBridge : lhs = rhs := by ...</code> and then <code>rw [hBridge]</code>.</span>

   - Prefer a named connector fact over a brittle inline <span style="color:gray">`have ->`</span> chain.

<a id="lean-review-bridge-order"></a>

## Canonical Bridge Order <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Show a typical route from indicator sum to count and bound. | moderate adaptation</span>
Preferred bridge sequence:

<span style="color:red"><strong>Why:</strong> The diagram uses MathComp sum/count syntax.<br><strong>Proposed change:</strong> Express its nodes with List.sum/countP or Finset.sum/filtered card. Finset.sum_boole can connect the indicator sum directly to cardinality.</span>

```text
\sum_(x <- s) (if P x then 1 else 0)
  ->
\sum_(x <- s | P x) 1
  ->
count P s
  ->
bound on count P s
  ->
bound on Nat.min / minn / final arithmetic expression
```

The hard rule is: do not skip a bridge when the next lemma lives in a different layer.

## Bridge Templates <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Show common local equality and bound templates.</span>

<a id="lean-review-template-1"></a>

### Template 1: Indicator Sum To Filtered Big Operator <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Expose the predicate as a filter.</span>
Use this when the branch still hides the predicate in `if ... then 1 else 0`.

<span style="color:red"><strong>Purpose:</strong> Prove that an indicator sum equals a filtered sum of ones.<br><strong>Proposed Lean adaptation:</strong> Replace MathComp sum notation and have syntax. Propose Finset.sum_filter for finite sets, or a list bridge preserving duplicates; a Lean local fact uses have with a by proof.</span>

```coq
have H_indicator_filter :
  \sum_(x <- s) (if P x then 1 else 0) = \sum_(x <- s | P x) 1.
(* Prove this local fact immediately with big_mkcond or the equivalent
   branch-local rewrite; do not leave a placeholder proof. *)
```

<a id="lean-review-template-2"></a>

### Template 2: Filtered Ones Sum To Count <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Turn a sum of ones into a count.</span>
Use this when the branch is already a filtered sum of ones.

<span style="color:red"><strong>Purpose:</strong> Turn the filtered sum of ones into the number of selected elements.<br><strong>Proposed Lean adaptation:</strong> Propose List.countP_eq_length_filter with simp, or cardinality simplification for Finset. For RTS sumFiltered, unfold its actual List-based definition from Prosa.Util.Sum.</span>

```coq
have H_filter_count :
  \sum_(x <- s | P x) 1 = count P s.
(* Prove this local fact immediately with sum1_count or a branch-local variant;
   do not leave a placeholder proof. *)
```

<a id="lean-review-template-3"></a>

### Template 3: Count Bound Before Min Bound <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Use a count bound to derive a minimum bound.</span>

<span style="color:red"><strong>Why:</strong> minn is a MathComp name.<br><strong>Proposed change:</strong> Use Nat.min; retain the count bound before deriving the minimum bound.</span>

Use this when the final statement mentions `Nat.min` or <span style="color:gray">`minn`</span>.

<span style="color:red"><strong>Purpose:</strong> First bound the count, then bound the corresponding minimum.<br><strong>Proposed Lean adaptation:</strong> Use a Lean local proof, List.countP or filtered Finset.card, and Nat.min. A bound can be transported with min_le_min_left; the business count bound still requires its original argument.</span>

```coq
have Hcount_bound : count P s <= k.
Proof.
  ...
Qed.

have Hmin_bound : Nat.min m (count P s) <= Nat.min m k.
Proof.
  ...
Qed.
```

Do not try to prove the `Nat.min` statement while the branch is still in indicator-sum form.

## Local Connector Fact Policy <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Name local connector facts for later reuse.</span>
For this proof class, local connector facts are usually better than long inline rewrites.

Preferred names:

- `H_indicator_filter`
- `H_filter_count`
- `Hcount_rest_tasks`
- `Hcount_exceeding_bound`
- `Hmin_count_bound`

Avoid a long script that repeatedly changes representation without naming the bridge.

<a id="lean-review-bool-prop"></a>

## Bool / Prop Separation <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Describe the original Bool-to-Prop arithmetic handoff; proposed removal.</span>

<span style="color:red"><strong>Proposed deletion boundary:</strong> Remove this subsection through Boundary Failure Signs, inclusive, only in a future Lean version. Ordinary Lean Nat comparisons are already Prop, so the fixed reflection roundtrip is unnecessary. All original material is retained below for review.</span>

These branches often have a second failure mode after the counting shape is already stable.

The branch is no longer stuck on <span style="color:gray">`big_mkcond`</span> or <span style="color:gray">`sum1_count`</span>, but it still fails because it keeps switching between:

- boolean comparison and <span style="color:gray">ssreflect reflection</span>
- Prop-level arithmetic needed for `lia`, `Nat.min`, or the final strict inequality

This section covers only the count-branch version of that problem.

<span style="color:gray">Use it when the branch is already about `count`, `Nat.min` or `minn`, or a final arithmetic inequality derived from a count bound.</span> If the branch is still drifting between indicator sum, filtered big operator, and count, finish that normalization first.

<a id="lean-review-problem-shape"></a>

### Problem Shape <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Illustrate the original reflection-related failure pattern.</span>
Typical sequence:

1. The proof establishes <span style="color:gray">a boolean fact such as `count P s < k`, `count P s <= k`, or `0 < x`</span>.
2. The next step needs Prop arithmetic, a `Nat.min` side condition, or a contradiction argument.

3. The script bounces among <span style="color:gray">`ltnW`, `ltnNge`, `move/ltP`, `move/leP`, `%coq_nat`</span>, and `lia` without committing to one layer.
4. The final arithmetic step fails even though the count argument is already essentially done.

The root cause is not that one specific lemma is missing.

<span style="color:gray">The branch crossed the bool/Prop boundary</span> without deciding which layer should own the rest of the proof.

### Boundary Rule <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Specify the original comparison-layer boundary.</span>

<span style="color:gray">Once the branch has a stable `count` or `Nat.min` expression, decide whether the rest of the branch should finish in:</span>

- <span style="color:gray">ssreflect boolean comparison form</span>
- Prop arithmetic form

<span style="color:gray">If the remaining work is final arithmetic, `Nat.min` side conditions, or `lia`, move to Prop exactly once</span> and stay there until that subproof closes. Do not alternate between boolean reflection and Prop arithmetic after the handoff.

<a id="lean-review-layer-map"></a>

### Layer Map <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Compare the original Bool and Prop representations.</span>
Use this rough split.

- bool layer

  - <span style="color:gray">`count P s < k`</span>
  - <span style="color:gray">`count P s <= k`</span>
  - <span style="color:gray">`ltnW`</span>
  - <span style="color:gray">`ltnNge`</span>
  - boolean rewriting and <span style="color:gray">reflection views</span>
- Prop layer

  - <span style="color:gray">`(count P s < k)%coq_nat`</span>
  - <span style="color:gray">`(count P s <= k)%coq_nat`</span>
  - `lia`

  - <span style="color:gray">`have -> : Nat.min a b = ... by lia`</span>
  - contradictions and transitivity using ordinary `<`, `<=`, or `=` hypotheses

<span style="color:gray">`ltnW` is usually a bool-side preparation step. Use it before the Prop handoff if you need a non-strict boolean fact.</span>

<a id="lean-review-handoff"></a>

### One-Way Handoff Protocol <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Sequence the original reflection handoff.</span>
1. Finish count normalization first.

   - The branch should already be in <span style="color:gray">`count`</span>, plain nat arithmetic, or `Nat.min` form.

2. <span style="color:gray">Isolate the last boolean fact you need.</span>
   - Typical examples: <span style="color:gray">`Hcount_lt : count P s < k`, `Hcount_le : count P s <= k`, `Hpos : 0 < x`</span>.
3. <span style="color:gray">Convert that fact into Prop exactly once.</span>
   - <span style="color:gray">`move/ltP: Hcount_lt => Hcount_lt_prop.`</span>
   - <span style="color:gray">`move/leP: Hcount_le => Hcount_le_prop.`</span>
4. Finish the remaining arithmetic entirely in Prop.
   - Use `lia`.
   - Rewrite `Nat.min` only after the side condition is already a Prop inequality.
5. Reflect back only if the final goal itself is a boolean comparison.

   - <span style="color:gray">`apply/ltP. exact Hgoal_prop.`</span>
   - <span style="color:gray">`apply/leP. exact Hgoal_prop.`</span>

<a id="lean-review-local-bridges"></a>

### Common Local Bridges <span style="color:red; font-size:14px; font-weight:normal; display:inline;">List the original reflection bridges.</span>
Use small local connectors rather than bouncing back and forth across the boundary.

- strict to non-strict <span style="color:gray">on the bool side</span>
  - <span style="color:gray">`have Hle_bool : a <= b by exact: ltnW Hlt_bool.`</span>
- bool to Prop

  - <span style="color:gray">`move/ltP: Hlt_bool => Hlt_prop.`</span>
  - <span style="color:gray">`move/leP: Hle_bool => Hle_prop.`</span>
- Prop back to a final bool goal

  - <span style="color:gray">`apply/ltP. exact Hlt_prop.`</span>
  - <span style="color:gray">`apply/leP. exact Hle_prop.`</span>

Do not use these bridges as an open-ended rewrite loop. Use them once to transfer ownership of the branch.

<a id="lean-review-template-4"></a>

### Template 4: Count Bound To Prop Arithmetic <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Move a count bound into Prop arithmetic.</span>
Use this when the count bound is done and only arithmetic remains.

```coq
have Hcount_lt : count P s < k.
Proof.
  ...
Qed.

have Hcount_lt_prop : (count P s < k)%coq_nat.
Proof.
  by move/ltP: Hcount_lt.
Qed.

have Hgoal_prop : (count P s < k + 1)%coq_nat.
Proof.
  lia.
Qed.

have Hgoal : count P s < k + 1.
Proof.
  apply/ltP.
  exact Hgoal_prop.
Qed.
```

<a id="lean-review-template-5"></a>

### Template 5: Prop Side Condition For Nat.min <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Prepare a side condition for a minimum.</span>
Use this when the count bound is already known, but `Nat.min` needs a Prop side condition.

```coq
have Hcount_le : count P s <= k.
Proof.
  ...
Qed.

have Hcount_le_prop : (count P s <= k)%coq_nat.
Proof.
  by move/leP: Hcount_le.
Qed.

have -> : Nat.min (count P s) k = count P s by lia.
```

If you prefer <span style="color:gray">`PeanoNat.Nat.min_l`</span> or <span style="color:gray">`PeanoNat.Nat.min_r`</span>, discharge the side condition only after it is already in Prop form.

<a id="lean-review-contradiction"></a>

### Contradiction Pattern With `ltnNge` <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Close a contradiction using the original Bool inequality API.</span>

Use <span style="color:gray">`ltnNge`</span> as a boundary-specific contradiction tool, not as a general rewrite strategy.

```coq
rewrite ltnNge.
apply/negP => /leP Hge_prop.
lia.
```

This is appropriate when the goal is a boolean strict inequality and the contradiction should finish in Prop arithmetic.

### Boundary Failure Signs <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Recognize failures in the original reflection workflow.</span>

The boundary was crossed at the wrong time if:

- <span style="color:gray">`lia` sees no usable arithmetic hypotheses because all comparisons are still boolean facts.</span>

- `Nat.min` or <span style="color:gray">`minn`</span> side conditions do not discharge because the branch still only has <span style="color:gray">`ltn`</span> or <span style="color:gray">`leq`</span> facts.
- the script proves a Prop inequality, immediately reflects it back to bool, then needs to move back to Prop again.

- the count argument is complete, but the strict inequality still fails because the branch never committed to one final layer.

<a id="lean-review-failure-signatures"></a>

## Failure Signatures For This Skill <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Map counting failures to checks. | substantial adaptation</span>

<span style="color:red"><strong>Why:</strong> These messages and intermediate forms come from Coq/MathComp.<br><strong>Proposed change:</strong> Treat them as historical examples. Rebuild Lean diagnostic entries only from observed errors, goals and declarations.</span>

- <span style="color:gray">`The LHS of big_mkcond ... does not match any subterm`</span>
  The branch is not yet in the expected indicator-sum head form.
- <span style="color:gray">`The LHS of sum1_count ... does not match any subterm`</span>
  The branch is not yet a filtered sum of ones.
- <span style="color:gray">`Unable to unify ... count ... with ... \sum_ ...`</span>
  The count bridge has not been established yet.

<span style="color:red"><strong>Why:</strong> The Coq message is not a Lean failure signature.<br><strong>Proposed change:</strong> Record the actual Lean diagnostic and remaining goals before assigning a cause.</span>

- <span style="color:gray">`No applicable tactic` after several bigop rewrites in a count argument</span>
  The proof is drifting across indicator, filter, and count forms without a stable target.
- A strict inequality fails after a count argument “should already be done”

  <span style="color:red"><strong>Why:</strong> Ordinary Lean Nat inequalities are already propositions.<br><strong>Proposed change:</strong> Remove this fixed Bool-to-Prop failure category together with the proposed deletion of the reflection subsection.</span>

  The arithmetic step is too early; the count layer or <span style="color:gray">the bool-to-Prop bridge</span> is not finished.

<a id="lean-review-anti-patterns"></a>

## Anti-Patterns <span style="color:red; font-size:14px; font-weight:normal; display:inline;">List approaches that obscure the chosen counting form. | moderate adaptation</span>
- Do not feed an indicator sum directly to a count lemma.

<span style="color:red"><strong>Why:</strong> minn is a MathComp identifier.<br><strong>Proposed change:</strong> Use Nat.min while keeping the warning against changing representations before the count is stable.</span>

- Do not apply `Nat.min` or <span style="color:gray">`minn`</span> lemmas before the raw count expression is stable.
- Do not bounce between filtered sequence form and count form without naming the connector fact.
- Do not start the final strict inequality proof while the branch still contains `if ... then 1 else 0`.

<span style="color:red"><strong>Why:</strong> Lean Nat comparisons need no reflection step before arithmetic.<br><strong>Proposed change:</strong> Remove the mandatory conversion restriction. Use an available arithmetic tactic on the actual goal; lia is available in the checked Lean version.</span>

- <span style="color:gray">Do not call `lia` while the main inequalities still only exist as `ltn` or `leq` facts.</span>
- Do not reflect back to bool in the middle of a Prop arithmetic subproof.

<span style="color:red"><strong>Why:</strong> ltnW and its prescribed position in a Bool-to-Prop handoff belong to MathComp.<br><strong>Proposed change:</strong> Remove that handoff requirement; use an ordinary Lean bound such as Nat.le_of_lt when needed.</span>

- <span style="color:gray">Do not use `ltnW` after the branch has already moved into Prop unless you are deliberately rebuilding a final bool goal.</span>

<span style="color:red"><strong>Why:</strong> The old min-side-condition advice assumes MathComp Bool comparisons.<br><strong>Proposed change:</strong> Supply ordinary Prop inequalities to Nat.min lemmas, for example Nat.min_eq_left, using the required orientation.</span>

- Do not rewrite `Nat.min` or <span style="color:gray">`minn`</span> while the only available side condition is still in boolean form.
- Do not encode theorem-local names such as `Hsum_slack` or `Hsum_succ` into the skill. Keep the skill at the proof-pattern level.
- Do not use this skill for focus drift or early-bound theorem application failures. Those are different problem classes.

## Minimal Debug Log <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Record the current expression, bridge and result.</span>

```text
Current counting shape:
Target normal form:
Next intended lemma:
Does that lemma live in indicator / filtered bigop / count / min-arithmetic layer:
Missing bridge step:
Named local connector fact:
Is the final arithmetic step still premature: yes/no
```

## Success Condition <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Define when the counting bridge is complete.</span>
This skill has worked when the branch stops oscillating between indicator sums, filtered big operators, counts, and `min` bounds, and every subsequent step stays inside one chosen counting normal form until the final arithmetic handoff.
