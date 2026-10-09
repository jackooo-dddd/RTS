---
name: lean-goal-driven-apply
description: 'Distinguish premises that `apply`/`refine` can leave as later goals from arguments Lean must know first (implicit data, `variable` arguments, policies, and type-class instances) when applying a Lean 4 lemma. Use when `apply` fails with "don''t know how to synthesize implicit argument", "typeclass instance problem is stuck", "failed to synthesize", or an application type mismatch before any ordinary premise appears, or when you are tempted to write a long fully explicit `exact @lemma …` term.'
argument-hint: '[lemma name] [goal shape or error]'
user-invocable: true
---

# Lean Goal-Driven Apply for Early-Bound Arguments

Use this skill for one failure mode: a library lemma looks applicable, but Lean cannot elaborate the application because some implicit argument, data argument, policy, or instance is not determined yet.

## Core Distinction

- **Postponable premises**: ordinary hypotheses of the lemma (`h : P`). `apply lemma` turns the ones it cannot fill into new goals; `refine lemma ?_ ?_` makes them explicit. Leave them as goals and prove them afterwards.
- **Early-bound arguments**: values Lean must know to state the rest of the lemma: a task or job, a policy, an arrival sequence, or a type-class instance whose type mentions them. If they stay metavariables, instance search is stuck and later hypotheses cannot even be type-checked.

If no ordinary premise goals have appeared yet, the problem is not "another premise to prove later".

## What Must Be Fixed First

An argument must be fixed first when it:

- appears in the type of an instance argument (`[JLFP Job]`, `[Interference Job]`, …), so instance search needs it;
- fixes the policy or model layer that later hypotheses are stated over;
- appears in the types of later hypotheses, so they cannot be stated until it is chosen.

`variable`s of the section become arguments of the lemma only if it uses them; check the real signature with `#check @lemma` (it shows every argument, implicit `{}` and instance `[]` ones included) or `lsp` hover.

## Failure Signals

- `don't know how to synthesize implicit argument 'tsk'`
- `typeclass instance problem is stuck, it is often due to metavariables`
- `failed to synthesize <Class> …` (the instance may exist but for a different, not-yet-unified argument)
- `application type mismatch` where a proof is passed where data was expected (argument order drift)
- the goals after `apply` include data goals such as `case tsk` or `?m.123` that you did not expect

## Procedure

1. Shape the local goal first (`show`, `unfold`), so its head matches the lemma's conclusion.
2. Try `apply lemma` (or `refine lemma ?_ ?_`) once in `lean_session`.
3. If Lean returns ordinary premise goals, stop filling arguments: prove those goals one by one.
4. If it fails before that, read `#check @lemma` and find the earliest argument Lean could not determine.
5. Supply only that argument, by name: `apply lemma (tsk := tsk) (arr_seq := arr_seq)`; named arguments do not depend on argument order.
6. Re-run. Once premise goals appear, go back to proving them.
7. If an instance is genuinely missing (not stuck), find it with `lean_query search`/`#synth`-style checks via the goal; do not add a new instance or hypothesis to the theorem.

## Hard Rule

Do not replace a nearly working `apply`/`refine` with a long, fully explicit term such as `exact @lemma _ _ tsk arr_seq _ _ h1 h2 h3 h4`. It forces you to reproduce the exact argument order, implicit arguments and instance placement at once, and it hides which premise is actually missing. Supply the one early-bound argument by name and keep the rest goal-driven.

## Preferred Application Style

```lean
  refine uniprocessor_response_time_bound (tsk := tsk) (arr_seq := arr_seq) ?_ ?_ ?_
  · exact h_arrivals_valid
  · exact h_sched_valid
  · intro j hj
    …
```

or

```lean
  apply uniprocessor_response_time_bound (tsk := tsk)
  all_goals first | assumption | skip
```

Then solve the remaining goals; check with `lean_session` which goals and in which order `apply` produced them.

## Postponable Example

A lemma `bounded_by_blocking (h_seg : ∀ j t1 t2, … → max_segment j t1 ≤ B (job_arrival j - t1)) : service_inversion_bounded tsk B`:

```lean
  have h_seg : ∀ j t1 t2, arrives_in arr_seq j → job_of_task tsk j →
      busy_interval_prefix arr_seq sched j t1 t2 →
      max_segment arr_seq j t1 ≤ blocking_bound ts tsk := by
    intro j t1 t2 h_arr h_tsk h_prefix
    exact nonpreemptive_segments_bounded_by_blocking h_arr h_tsk h_prefix
  exact bounded_by_blocking h_seg
```

The premise `h_seg` is an ordinary hypothesis: prove it as its own `have` (or leave it as a goal of `apply`); do not try to fix it before applying.

## Anti-Patterns
- Treating a stuck instance as a missing hypothesis and adding an assumption to the theorem.
- Writing the whole explicit application from memory instead of reading `#check @lemma`.
- Filling premises before the early-bound data is fixed.
- Supplying arguments positionally when named arguments would avoid order drift.

## Success Condition
Lean elaborates the application, the remaining goals are only ordinary premises, and each is proved from the context or a named bridge fact.
