<span style="color:red"><strong>Purpose:</strong> Diagnose why a seemingly relevant theorem will not apply. Distinguish missing inputs, such as a scheduling model or typeclass instance, from assumptions that can become separate proof goals. Inspect the full theorem type and supply only inputs that inference cannot determine.</span>

<span style="color:red"><strong>Required interface review:</strong> The examples use concrete Prosa models and large theorem signatures. Their Lean binders and instance inference must be checked against RTS; translating tactic syntax or copying positional arguments is insufficient. Keep the distinction between data, instances and proof premises. All original examples remain review material.</span>

---
name: coq-goal-driven-apply
#<span style="color:red"><strong>description recommendation:</strong> For a future Lean version, describe unresolved theorem arguments or instances versus remaining proof premises. Reason: the actual Lean signature and inference determine the missing input.</span>
description: Distinguish postponable proof obligations from non-postponable early-bound implicit parameters, section arguments, policies, and typeclass instances in Coq and Rocq theorem application. In this failure mode, do not use exact of a fully explicit theorem term as a workaround. Use when apply or eapply fails before ordinary subgoals appear and Coq reports uninstantiated existentials or instance-construction errors, or when you are tempted to write a long exact (@lemma ...) call.
argument-hint: '[theorem name] [goal shape or early-binding error]'
user-invocable: true
---

# Coq Goal-Driven Apply for Early-Bound Arguments <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Distinguish unresolved theorem inputs from unproved premises.</span>

<span style="color:red"><strong>Why:</strong> The introduction describes Coq application behavior.<br><strong>Proposed change:</strong> Recheck the actual Lean declaration and application result; retain the distinction between missing arguments and unproved premises.</span>

Use this skill for one failure mode only: an exported lemma looks applicable, but <span style="color:gray">Coq</span> cannot even produce the ordinary proof obligations because some implicit parameter, section argument, policy, or typeclass instance has not been fixed yet.

<a id="lean-review-1"></a>

## Core Distinction <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Separate arguments needed for application from later proof goals. | minor adaptation</span>

There are two very different kinds of missing information.

<span style="color:red"><strong>Why:</strong> apply:/eapply are Coq application forms.<br><strong>Proposed change:</strong> Use Lean apply/refine to expose premises, supplying only arguments that the actual Lean elaborator cannot infer.</span>

- Postponable proof obligations: ordinary premises that appear as subgoals after <span style="color:gray">`apply:` or `eapply`</span>. These should stay postponed.
- Early-bound arguments or instances: values <span style="color:gray">Coq</span> must know before the theorem term is well-typed. These cannot be postponed.

<span style="color:red"><strong>Why:</strong> Coq application outcomes do not establish what Lean will infer.<br><strong>Proposed change:</strong> Inspect the current Lean goals and diagnostics before classifying the missing information.</span>

If <span style="color:gray">Coq</span> has not produced ordinary subgoals yet, do not treat the problem as just another premise to prove later.

<a id="lean-review-2"></a>

## What Must Be Fixed First <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Identify inputs that application cannot infer. | moderate adaptation</span>

An implicit argument or instance must be fixed first if it does one of the following:

<span style="color:red"><strong>Why:</strong> The Coq Instance declarations cannot be copied into Lean.<br><strong>Proposed change:</strong> Use the actual RTS Interference and InterferingWorkload classes with an appropriate local typed let/letI; verify synthesis in the current context.</span>

- determines a local <span style="color:gray">`Instance`</span> used in the theorem statement
- fixes the policy that later hypotheses are typed over

<span style="color:red"><strong>Why:</strong> Translation can change binders and inference dependencies.<br><strong>Proposed change:</strong> Inspect the real Lean declaration with #check/#print; do not copy the Coq positional argument order.</span>

- appears in the type of later hypotheses, so <span style="color:gray">Coq</span> cannot state those hypotheses until the binder is chosen
- selects the `Interference`, `InterferingWorkload`, readiness, or policy layer in which the conclusion lives

<a id="lean-review-3"></a>

## Failure Signals <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Inspect failures that may indicate missing arguments or instances. | substantial adaptation</span>

Use this skill when goal-driven apply fails with signals like these:

<span style="color:red"><strong>Why:</strong> These messages come from Coq.<br><strong>Proposed change:</strong> Use genuine Lean diagnostics together with the full declaration and current goal.</span>

- <span style="color:gray">`Not enough uninstantiated existential variables.`</span>
- <span style="color:gray">`Constant does not build instances of a declared type class.`</span>

<span style="color:red"><strong>Why:</strong> The quoted type mismatch uses the Coq interface.<br><strong>Proposed change:</strong> Compare the actual expected Lean type with the supplied term to distinguish data, instances and proofs.</span>

- <span style="color:gray">Coq</span> expects a policy, instance, or data argument, but your next term is a proof hypothesis.
- A proof term such as `REFLEXIVE_JLFP` or `WORK_BEARING` is being read as if it should fill a non-`Prop` binder.

These are early-binding failures. They are not ordinary missing premises.

<a id="lean-review-4"></a>

## Procedure <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Inspect the declaration, supply missing inputs and retry. | moderate adaptation</span>

1. Shape the local goal first.

<span style="color:red"><strong>Why:</strong> The first application uses Coq tactic syntax and inference.<br><strong>Proposed change:</strong> Try the appropriate Lean apply/refine, then inspect what remains unresolved before supplying arguments.</span>

2. Try <span style="color:gray">`apply:` or `eapply`</span> exactly once.
3. If <span style="color:gray">Coq</span> exposes ordinary subgoals, stop. Those goals are postponable. Keep them postponed.
4. If <span style="color:gray">Coq</span> fails before ordinary subgoals appear, inspect the theorem source and identify the earliest non-inferable binder or instance.

<span style="color:red"><strong>Why:</strong> The retry must respect Lean binder and instance inference.<br><strong>Proposed change:</strong> Provide the missing named argument or local instance, then retry apply/refine in the same goal.</span>

5. Add only that earliest binder or instance explicitly, <span style="color:gray">while keeping the theorem application in `apply:` or `eapply` form</span>.
6. Re-run <span style="color:gray">`apply:` or `eapply`</span>.
7. Once <span style="color:gray">Coq</span> starts exposing ordinary subgoals, switch back to postponed-proof mode and do not keep filling parameters.

<a id="lean-review-5"></a>

## Hard Rule <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Make application failures explicit before writing more proof steps.</span>

For this failure mode, `exact (@lemma ...)` is prohibited as a repair strategy.

<span style="color:red"><strong>Why:</strong> The application syntax is Coq-specific.<br><strong>Proposed change:</strong> Use Lean apply/refine when exposing proof premises is helpful. Broader objections to explicit terms are recorded separately as original-skill issues.</span>

- Do not replace a failed or nearly working <span style="color:gray">`apply:` or `eapply`</span> with a fully explicit theorem term.
- Do not use `exact (@lemma ...)` just to force <span style="color:gray">Coq</span> past unresolved policies, instances, or generalized binders.
- If <span style="color:gray">`apply:` or `eapply`</span> already exposes ordinary subgoals, then the explicit `exact (@lemma ...)` form is strictly worse and should be rejected.

The reason is procedural, not stylistic: a long explicit term bypasses obligation discovery. It turns a goal-driven proof into manual reconstruction of the theorem's exported binder order, instance placement, and policy choices.

<a id="lean-review-6"></a>

## Preferred Application Style <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Prefer applications whose remaining premises are visible.</span>

<span style="color:red"><strong>Why:</strong> Goal-directed inference depends on the translated declaration.<br><strong>Proposed change:</strong> Use the actual Lean theorem and let its conclusion constrain arguments; name only unresolved inputs.</span>

When the theorem head is already the right one, keep the application implicit and let <span style="color:gray">Coq</span> expose the remaining obligations.

Prefer:

<a id="lean-review-code-1"></a>

<span style="color:red"><strong>Purpose:</strong> Apply the final theorem and leave its proof premises as goals.<br><strong>Proposed Lean adaptation:</strong> Use the actual RTS AbstractSeqRta.uniprocessor_response_time_bound_restricted_supply_seq declaration with Lean apply/refine; inspect its complete namespace and inputs.</span>

```coq
eapply uniprocessor_response_time_bound_restricted_supply_seq.
all: try done.
```

or:

<a id="lean-review-code-2"></a>

<span style="color:red"><strong>Purpose:</strong> Use a short application so the goal supplies inferable arguments.<br><strong>Proposed Lean adaptation:</strong> Replace apply: and SSReflect closing syntax with Lean apply/refine and suitable assumption steps; inspect the remaining premises.</span>

```coq
apply: uniprocessor_response_time_bound_restricted_supply_seq => //.
```

Then solve the exposed goals one by one.

Avoid replacing a nearly working application with a full explicit term such as:

<a id="lean-review-code-3"></a>

<span style="color:red"><strong>Purpose:</strong> Show how a long positional application can obscure argument alignment.<br><strong>Proposed Lean adaptation:</strong> Inspect the actual Lean binder order and types. Prefer named unresolved inputs; an explicit proof term is not inherently invalid.</span>

```coq
exact (@uniprocessor_response_time_bound_restricted_supply_seq
   Task H ...
   INTRA_BOUNDED R SOL_SEQ_RS
   j ARR TSK).
```

That style is brittle because it forces you to guess generalized binder order, policy choices, and instance placement all at once. One small drift in a threshold instance, interference instance, or policy coercion can make the entire term ill-typed.

<span style="color:red"><strong>Why:</strong> The retry shown is a Coq call.<br><strong>Proposed change:</strong> Retry the actual Lean call after the missing argument or instance has been supplied.</span>

If one early-bound item really must be fixed first, add only that item and then <span style="color:gray">return immediately to `apply:` or `eapply`</span>. Do not keep expanding the theorem term.

<a id="lean-review-7"></a>

## Postponable Example <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Show premises that can remain as proof goals.</span>

<a id="lean-review-code-4"></a>

<span style="color:red"><strong>Purpose:</strong> Obtain a nonpreemptive-segment bound before applying the service-inversion theorem.<br><strong>Proposed Lean adaptation:</strong> Use the actual RTS declarations in Facts.BlockingBound.Fp and Facts.BusyInterval.ServiceInversion. Verify required priority instances; FP_to_JLFP is not an automatic global instance.</span>

```coq
have H_pi_bounded :
   forall j0 t1 t2,
      arrives_in arr_seq j0 ->
      job_of_task tsk j0 ->
      busy_interval_prefix arr_seq sched j0 t1 t2 ->
      max_lp_nonpreemptive_segment arr_seq j0 t1 <=
         (fun _ => blocking_bound ts tsk) (job_arrival j0 - t1).
Proof.
   move=> j0 t1 t2 ARR0 TSK0 PREFIX.
   exact: nonpreemptive_segments_bounded_by_blocking.
Qed.

have SI_BOUNDED :
   service_inversion_is_bounded_by arr_seq sched tsk (fun _ => blocking_bound ts tsk).
Proof.
   apply: service_inversion_is_bounded => //.
   exact: H_pi_bounded.
Qed.
```

Here `H_pi_bounded` is a normal proof premise. It appears after the theorem application and can be discharged later. Do not make more parameters explicit.

<a id="lean-review-8"></a>

## Early-Bound Example <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Show model instances needed before application can proceed.</span>

This is an existing-context pattern, not code to add to the benchmark file.
If the surrounding file or imported library already provides:

<span style="color:red"><strong>Why:</strong> The example depends on concrete Prosa instance definitions, not interchangeable placeholder APIs.<br><strong>Proposed change:</strong> Use the RTS rs_jlfp_interference and rs_jlfp_interfering_workload definitions from IwInstantiation, with their existing context, including JobCost. Verify any required local priority coercion.</span>

```text
JLFP : JLFP_policy Job
H_priority_is_reflexive : reflexive_job_priorities JLFP
rs_jlfp_interference : Interference Job
rs_jlfp_interfering_workload : InterferingWorkload Job
H_policy_respects_sequential_tasks : policy_respects_sequential_tasks JLFP
```

then a target such as:

<a id="lean-review-code-5"></a>

<span style="color:red"><strong>Purpose:</strong> Supply the interference model used by the sequential-task consistency property.<br><strong>Proposed Lean adaptation:</strong> Use the actual RTS IBF.Task.interference_and_workload_consistent_with_sequential_tasks declaration and its Interference/InterferingWorkload instances; do not copy Coq argument order.</span>

```coq
interference_and_workload_consistent_with_sequential_tasks arr_seq sched tsk
```

may require fixing the policy or instance arguments before ordinary proof
premises appear.

<span style="color:red"><strong>Why:</strong> Context/Hypothesis/Parameter/Variable are Coq declarations.<br><strong>Proposed change:</strong> Use the corresponding existing Lean binders or instances; preserve the ban on inventing premises to repair application.</span>

Do not introduce new <span style="color:gray">`Context`, `Hypothesis`, `Parameter`</span>, or
<span style="color:gray">`Variable`</span> declarations to manufacture these arguments.

In this shape, `JLFP` and the induced `Interference` and `InterferingWorkload` instances are not later proof obligations.

<span style="color:red"><strong>Why:</strong> What Coq must resolve early is not necessarily what Lean leaves unresolved.<br><strong>Proposed change:</strong> Determine missing Lean inputs from its actual elaboration result, rather than copying the old classification.</span>

<span style="color:gray">Coq must know them before it can form the instantiated theorem term.</span> If they are still ambiguous, do not start filling later premises such as `SI_BOUNDED` or workload bounds. First fix the missing policy or instance, then re-run the theorem application.

<a id="lean-review-9"></a>

## Final-Theorem Example <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Inspect a large RTS theorem before applying it.</span>

Suppose the final goal already matches a theorem head like
`uniprocessor_response_time_bound_restricted_supply_seq` and the remaining work is to supply facts such as schedule validity, bounded interference, a valid SBF, and a recurrence solution.

Preferred script:

<a id="lean-review-code-6"></a>

<span style="color:red"><strong>Purpose:</strong> Apply the final response-time theorem against the current goal.<br><strong>Proposed Lean adaptation:</strong> Check the translated theorem in Abstract.RestrictedSupply.AbstractSeqRta, including its data, instances and proof premises.</span>

```coq
eapply uniprocessor_response_time_bound_restricted_supply_seq.
all: try done.
```

Then inspect the remaining goals and solve them using the local facts you already named.

If the proof can be driven by a line such as:

<a id="lean-review-code-7"></a>

<span style="color:red"><strong>Purpose:</strong> Let a short theorem application infer inputs from the goal.<br><strong>Proposed Lean adaptation:</strong> Use Lean apply/refine with the actual declaration and check which goals it produces.</span>

```coq
apply: uniprocessor_response_time_bound_restricted_supply_seq; try done.
```

then a fully explicit `exact (@uniprocessor_response_time_bound_restricted_supply_seq ...)` term is not merely verbose. In this skill, it is the wrong move and should be removed.

Do not jump directly to:

<a id="lean-review-code-8"></a>

<span style="color:red"><strong>Purpose:</strong> Illustrate an unwieldy positional application mixing model inputs and proofs.<br><strong>Proposed Lean adaptation:</strong> Read the Lean declaration and name unresolved inputs instead of mechanically translating this positional list.</span>

```coq
exact (@uniprocessor_response_time_bound_restricted_supply_seq
   Task H ...
   ABSTRACT_WORK_CONSERVING H_sequential_tasks I_AND_W_SEQUENTIAL
   L BUSY_INTERVALS_BOUNDED (arm_sbf Π Θ ν)
   RS_VALID_BUSY_SBF_ARM ARM_SBF_UNIT
   ...
   j ARR TSK).
```

<span style="color:red"><strong>Why:</strong> The final theorem has a translated Lean interface.<br><strong>Proposed change:</strong> Inspect the actual RTS AbstractSeqRta declaration, its instances and premises before proposing a call.</span>

In this situation, a long explicit term is not helping <span style="color:gray">Coq</span> discover obligations. It is bypassing obligation discovery and making you manually reconstruct the theorem's full exported binder order.

Concrete replacement example:

<a id="lean-review-code-9"></a>

<span style="color:red"><strong>Purpose:</strong> Show the final theorem inputs, instances and proof premises.<br><strong>Proposed Lean adaptation:</strong> Use the actual RTS declaration. Do not equate a structured SupplyBoundFunction value with its numeric function field or assume the Coq binder list survives translation.</span>

```coq
exact (@uniprocessor_response_time_bound_restricted_supply_seq
   Task H (@limited_preemptions_rtc_threshold Task H H1)
   Job H2 H4 H3 (@limited_preemptive_job_model Job H5)
   PState H_uniprocessor_proc_model H_unit_supply_proc_model
   H_consumed_supply_proc_model arr_seq VALID_ARRIVALS
   sched JOBS_FROM_ARRIVAL_SEQUENCE JOBS_MUST_ARRIVE
   COMPLETED_JOBS_DONT_EXECUTE VALID_COSTS ts tsk H_tsk_in_ts
   VALID_PREEMPTION_MODEL VALID_RTCT H0 VALID_ARRIVAL_CURVE
   RESPECTS_MAX_ARRIVALS
   (rs_jlfp_interference arr_seq sched)
   (rs_jlfp_interfering_workload arr_seq sched)
   ABSTRACT_WORK_CONSERVING H_sequential_tasks I_AND_W_SEQUENTIAL
   L BUSY_INTERVALS_BOUNDED (arm_sbf Π Θ ν)
   RS_VALID_BUSY_SBF_ARM ARM_SBF_UNIT
   (fun _ F => blocking_bound ts tsk + total_ohep_request_bound_function_FP ts tsk F)
   INTRA_BOUNDED R SOL_SEQ_RS
   j ARR TSK).
```

should be replaced by:

<a id="lean-review-code-10"></a>

<span style="color:red"><strong>Purpose:</strong> Replace a long argument list with application and explicit remaining goals.<br><strong>Proposed Lean adaptation:</strong> Propose Lean apply/refine, optionally followed by all_goals try assumption, then prove the actual remaining premises.</span>

```coq
apply: uniprocessor_response_time_bound_restricted_supply_seq; try done.
```

<span style="color:red"><strong>Why:</strong> The stated inference result is specific to the Coq call.<br><strong>Proposed change:</strong> Check which arguments Lean infers and which proof goals its actual application creates.</span>

This shorter script is stronger because it lets <span style="color:gray">Coq</span> recover the instantiated theorem head from the goal and generate only the real remaining obligations.

<a id="lean-review-10"></a>

## Anti-Patterns <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Avoid guessing arguments or disguising inference failures. | minor adaptation</span>

- Do not respond to early-binding errors by writing a full `@lemma ...` term.

<span style="color:red"><strong>Why:</strong> apply:/eapply and try done are Coq forms, and semicolon behavior differs.<br><strong>Proposed change:</strong> Use apply/refine and, when appropriate, all_goals try assumption. Obtain argument names from the actual Lean declaration.</span>

- Do not replace a good <span style="color:gray">`apply:` or `eapply`</span> candidate with `exact (@lemma ...)` just because some parameters are still unresolved.
- Do not keep an `exact (@uniprocessor_response_time_bound_restricted_supply_seq ...)` script once <span style="color:gray">`apply: uniprocessor_response_time_bound_restricted_supply_seq; try done.`</span> works.
- Do not fill later proof premises when the theorem term itself is still ambiguous.
- Do not treat a typeclass-construction failure as evidence that more `Prop` goals should be proved.
- Do not keep adding explicit arguments after the first missing policy or instance has been identified.

<a id="lean-review-11"></a>

## Output Expectations <span style="color:red; font-size:14px; font-weight:normal; display:inline;">Report the missing input and the evidence for the diagnosis. | moderate adaptation</span>

When using this skill, explain proof choices in this order:

<span style="color:red"><strong>Why:</strong> A Coq trace cannot certify the current Lean application state.<br><strong>Proposed change:</strong> Report the observed Lean error/goals, missing input, reason, proposed repair and validation result.</span>

1. whether <span style="color:gray">Coq</span> already exposed ordinary proof obligations
2. which binder or instance must be fixed first
3. why that item is not a postponable proof premise
4. what minimum explicit information should be added now
5. when it is safe to return to postponed-proof mode
