# New: statement-equivalence service in `lean_session` (Pantograph)

**Implements**: DECISIONS D10 (K6, K7). **Builds on**: `tools-advices/01-core-tools/coq-session-revision.md` §6 (the
entry-goal check of upstream 8e1de8c), BACKEND_DECISION.md.

An internal function (not a model-facing operation) used by `proof-plan.ts` and `proof-workflow.ts`:

```
equivalent(file, theorem, a: string, b: string) -> "equivalent" | "different" | "a_does_not_elaborate" | "b_does_not_elaborate" | "backend_error"
elaborates(file, theorem, a: string) -> ok | error
```

- Context: the target theorem's context in the staged file (its binders, `variable`s, instances, namespaces), opened
  through Pantograph — the same context the region will be proved in.
- Test: elaborate both strings as `Prop`; `isDefEq` at default transparency. First a cheap text pass
  (`normalizeGoal`-style); only call Lean if the texts differ.
- Pantograph 0.3.19 has no stand-alone definitional-equality command. Run the tactic `show <b>` on a goal state
  whose target is `a` (`goal.tactic {"stateId": s, "goalId": g, "tactic": "show <b>"}`): `show` elaborates `b`
  in that goal's local context and succeeds only if it is defeq to the target. Pantograph states are immutable, so
  the check never changes the agent's state. For two free-standing strings, open `a` with `goal.start` in the
  theorem's context first.
- Limits: prefix the tactic with `set_option maxHeartbeats 200000 in` and set the Pantograph `timeout` option
  (`options.set {"timeout": <ms>}`); both are cooperative, so the tool also enforces a wall-clock limit and
  restarts the process when it is exceeded. Any limit hit is `backend_error`.
- Results are cached by (source hash, theorem, a, b). `backend_error` is a tool error: it never counts as drift and
  never spends a planning revision.
- Security: `a`/`b` must be pure terms (no `by`, no commands, no `#`-commands) — same rule as the entry-goal check.
- **No holes.** `show b` unifies, so a `b` containing `_`, `?x` or `?_` matches almost anything and would be
  reported `equivalent`. A check for leftover metavariables after `show` does not help: unification has assigned
  them. So, before any check, scan `b` (and `a`) **token by token, never as a substring**:
  - Split the text with Lean's identifier rules: an identifier starts with a letter or `_` and continues with
    letters, digits, `_`, `'`, `!`, `?` and subscripts, may have `.`-separated parts, and may be quoted `«…»`.
    Underscores *inside* identifiers are ordinary (`Lemma3_05_statement`, `job_cost`, `task_cost`), and so is a
    trailing `?`/`!` (`List.get?`, `Option.get!`).
  - Reject a **term hole**: `_` as a standalone token (not part of an identifier) in term position; a `?` that
    *starts* a token and is followed by an identifier or `_` (`?x`, `?_`) in term position; the identifiers
    `sorry` and `sorryAx`. A standalone `_` as a binder name stays allowed (`fun _ =>`, `∀ _,`, `∃ _,`, `(_ : T)`).
  - Allow **universe-level metavariables**: pretty-printed goals occasionally show an unsolved level such as
    `Sort ?u.123`, `Type ?u.123` or `.{?u.123}`. In a universe position (after `Sort`/`Type`, inside `.{…}`) such a
    `?u.N` is replaced by the level hole `_` before elaboration instead of being rejected. A level hole can only
    generalise a universe, not absorb a subterm, and the frozen statement is still what `check.py` proves. The
    tool's own goal printing uses the theorem's level names (`u`, `v`), so this should be rare.
  - On rejection report `b_does_not_elaborate` with the offending token. Genuine statements (pretty-printed goals,
    Prosa names) contain no term holes, so they are not affected.

  The same rule applies to `normal_form`, `root_goal` and the entry-goal check (tools-advices
  `coq-session-revision.md` §6). Backstop, to confirm in the
  spike: elaborate `b` alone first — `expr.echo {"expr": b, "type": "Prop", "levels": …}` for a closed root goal,
  or `have _probe : (b) := sorry` on the region's goal state — which fails with "don't know how to synthesize
  placeholder" when a hole is left.

## Root goal: the statement is a constant

Every benchmark task has the form (all 24 `Solution.lean` files):

```lean
universe u v                                   -- `universe u` for BOOK2015 Theorem18_6
theorem solution : Lemma3_05_statement.{u, v} := by
  sorry
```

where `def Lemma3_05_statement : Prop := ∀ …` is in the read-only `Statement.lean`. Consequences:

1. **Opening the root goal.** `solution` is not in the environment while its proof is `sorry` in the staged file,
   so `copyFrom` cannot be used. Open the root with
   `goal.start {"expr": "<qualified statement name>.{u, v}", "levels": ["u", "v"]}`, taking the level names from
   the `universe` line of `Solution.lean` (or from the constant's level parameters via `env.inspect`). The opened
   goal is the bare constant.
2. **What the agent and the plan see.** The first step on the root goal is one delta step
   (`unfold <thm>_statement`), which gives the `∀ …` proposition. The plan's `root_goal`, the snapshot shown to the
   agent, and every pretty-printed root goal use this unfolded form, so the model is never asked to restate the
   bare constant.
3. **Comparison.** The cheap text pass compares the plan's `root_goal` with the pretty-printed *unfolded* statement
   (comparing with the `Solution.lean` text can never match). The elaboration check runs `show <root_goal>` on the
   goal opened in step 1; `isDefEq` unfolds the constant at default transparency, so both the folded and the
   unfolded forms are accepted.
4. **Universe parameters.** Every elaboration (root goal, `normal_form`, region targets) happens in a context that
   declares the same level names; a `root_goal` that fixes a universe (`Type 0` instead of `Type u`) is
   `different`, not a formatting difference.
5. **Region goals** come from `frontend.distil` on the staged file's *body* (import lines stripped, REPL started
   with exactly those imports, every region that does not check replaced by `sorry`); the goal states carry the
   local context and the theorem's universe levels. Procedure and the open point about mapping goals to
   `admit_id`s: BACKEND_DECISION *Implementation answers* and *First spike*.
