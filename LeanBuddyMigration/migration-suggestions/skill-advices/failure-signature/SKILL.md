<span style="color:red"><strong>Purpose:</strong> Turn hard-to-read rewrite errors into a short list of things to inspect. For example, a failed multiplication rewrite may mean the expression is still a sum; the table suggests checking the current expression before choosing another step.</span>

<span style="color:red"><strong>Proposed deferral:</strong> <a href="#lean-review-2">Common Messages</a> uses Coq errors and MathComp intermediate forms as its classifier. Lean may produce different errors and goals, so translating the code alone would not validate the table. Omit this lookup skill from the future Lean version until real Lean/ProsaBuddy runs provide reproducible cases.</span>

<span style="color:red"><strong>About the example:</strong> <a href="#lean-review-3">Diagnostic Example</a> concerns num_cpus copies of a constant X. It shows a starting goal, one rewrite and a possible iter goal; it contains no failing command or actual diagnostic output. The original table and all examples remain here as review material.</span>

---
name: coq-failure-signatures
#<span style="color:red"><strong>description recommendation:</strong> Defer the Lean lookup skill until actual Lean errors and validated repairs exist. If rebuilt, describe those observed cases rather than Coq error strings.</span>
description: Use when Coq or ssreflect rewrite errors are hard to interpret and you need error-message-to-action mappings for shape mismatches.
argument-hint: '[error message] [current goal form]'
user-invocable: true
---

# Failure Signatures <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Explain rewrite errors through a short lookup reference.</span>

<span style="color:red"><strong>Why:</strong> Coq/SSReflect error strings are not Lean failure signatures.<br><strong>Proposed change:</strong> Defer this lookup skill for the future Lean version until real Lean/ProsaBuddy runs support a replacement table.</span>

This reference maps <span style="color:gray">common Coq and ssreflect rewrite errors</span> to the missing normalization step.

<a id="lean-review-1"></a>

## Read the Error as a Shape Mismatch <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Compare the actual goal with the intended rewrite.</span>
Treat most failed rewrites as evidence that the current goal shape is different from the one in your head.

<a id="lean-review-2"></a>

## Common Messages <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Map historical error messages to possible next steps. | major rewrite proposed</span>

<span style="color:red"><strong>Why:</strong> The table classifies failures using Coq errors and MathComp iter/ordinal states. Translating examples alone would leave those classifications unsupported.<br><strong>Proposed change:</strong> Keep this table as historical material. Rebuild only from real Lean diagnostics, goals, declarations and validated repairs.</span>

| Error message | What it means | What to do next |
|---|---|---|
| <span style="color:gray">`Unable to unify "X * n" with "iter n (addn X) 0"`</span> | <span style="color:gray">A constant big operator has already reduced to `iter`, but not yet to multiplication.</span> | <span style="color:gray">Finish the `iter` normalization, or rewrite the other side back to big operator form first.</span> |
| <span style="color:gray">`The LHS of mul1n ... does not match any subterm`</span> | There is no literal `1 * _` in the goal. | Do not apply <span style="color:gray">`mul1n`</span> yet. First reduce the branch or constant sum until `1 * _` actually appears. |
| <span style="color:gray">`The LHS of mulnC ... does not match any subterm`</span> | There is no multiplication node yet, or it is not the subterm you intended. | Inspect the goal and <span style="color:gray">confirm whether you are still in `bigop` or `iter` form</span>. |
| <span style="color:gray">`The LHS of big_ord_recr ... does not match any subterm`</span> | The goal is no longer <span style="color:gray">a standard ordinal big operator head</span>. | <span style="color:gray">Restore a `\sum_(i < n)` shape before peeling the first term.</span> |
| <span style="color:gray">`No applicable tactic` after several rewrites</span> | The proof has drifted across multiple equivalent forms without a stable intermediate target. | Freeze the current goal, choose one normal form, and add a bridge lemma toward it. |

<a id="lean-review-3"></a>

## Diagnostic Example <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Inspect the goal before and after a constant-sum rewrite.</span>

If the goal started as:

<a id="lean-review-code-1"></a>

<span style="color:red"><strong>Purpose:</strong> State that adding num_cpus copies of X equals X times num_cpus.<br><strong>Proposed Lean adaptation:</strong> A future Lean illustration could use a sum indexed by Fin num_cpus. This original block states a goal; it is not an error message.</span>

```coq
\sum_(cpu < num_cpus) X = X * num_cpus
```

then after:

<a id="lean-review-code-2"></a>

<span style="color:red"><strong>Purpose:</strong> Rewrite the constant MathComp sum and inspect its new form.<br><strong>Proposed Lean adaptation:</strong> big_const_ord is not a Lean lemma. A future example must show its actual Lean rewrite and output rather than assume the same intermediate form.</span>

```coq
rewrite big_const_ord.
```

the proof state may become:

<a id="lean-review-code-3"></a>

<span style="color:red"><strong>Purpose:</strong> Show the possible Coq iter goal after that rewrite.<br><strong>Proposed Lean adaptation:</strong> This is a proof state, not a reported error. The analogous Lean constant sum can simplify with Nat.mul_comm, so a diagnostic example must come from a real Lean failure instead.</span>

```coq
iter num_cpus (addn X) 0 = X * num_cpus
```

At that point:

<span style="color:red"><strong>Why:</strong> These follow-up actions assume the Coq iter state shown above.<br><strong>Proposed change:</strong> Do not carry the too-early/too-late diagnoses into Lean without observing its actual intermediate goal.</span>

- <span style="color:gray">`mulnC` is too early if multiplication is not yet on the left.</span>
- <span style="color:gray">`big_ord_recr` is too late because the left side is no longer a big operator.</span>
- <span style="color:gray">the correct move is a bridge step from `iter` to multiplication</span>, or a different earlier normalization plan.

<a id="lean-review-4"></a>

## Practical Rule <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Record the goal and proposed rewrite before acting.</span>
Before each rewrite, write down:

```text
Current head form:
Lemma left-hand side:
Does the left-hand side literally occur in the goal?
```

If the answer is no, add a bridge lemma instead of trying another algebraic rewrite.
