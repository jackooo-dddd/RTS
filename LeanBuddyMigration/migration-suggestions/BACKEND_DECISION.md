# Backend Decision: Pantograph, Lean LSP, and `lake build`

**Status: decided (2026-10-09).** This closes GAPS.md §6 and README "Structural Changes to Settle First" item 2.

## Decision

- **Pantograph is the primary interactive proof backend.** It replaces ProsaBuddy's `coq_session` and `petanque`.
  Pantograph is built for AI-driven interactive theorem proving in Lean 4: an agent can run tactics step by step,
  inspect the resulting goals, manage several subgoals, and go back to an earlier proof state when a tactic fails.
  This matches ProsaBuddy's workflow, where helpers explore proof strategies, inspect intermediate states and
  recover from failures before committing anything to the source file. The Lean REPL offers similar features, but
  its tactic mode is still experimental, while Pantograph is specialised for automated proof search.
- **Lean LSP handles file-level diagnostics** (errors and warnings of the current source revision, plus read-only
  hover, go-to-definition and references). It is not used to execute tactics.
- **`lake build` performs final verification.** A proof counts as complete only after the module builds in the
  project environment and passes the integrity audit (see KNOWN_PROBLEMS K9).

## Responsibilities

| ProsaBuddy component (Rocq) | Lean replacement | Notes |
|---|---|---|
| `coq_session` open / step / goal / snapshot / undo | Pantograph goal states | Step = run a tactic on a goal state; snapshot = keep the state handle; undo = continue from an earlier handle. |
| `petanque` start / run / goals | Pantograph (same tool) | Merge `petanque` into the Pantograph-backed session tool; keep one interactive tool, not two. |
| Entry-goal check by kernel conversion (`eq_refl`, upstream 8e1de8c) | `isDefEq` between the live goal and the elaborated expected goal, evaluated in the goal's local context through Pantograph | See `tools-advices/01-core-tools/coq-session-revision.md` §6. |
| `coqtop` queries (`Check`, `Print`, `About`, `Search`) | Pantograph environment/expression queries, or `#check`/`#print` in a scratch check; repository search for names | Queries must run in the target's real context (namespaces, `variable`s, instances). |
| LSP `proofGoals`, `LSP.rocqGoals` in proof-context | Removed (D3): the `lsp` tool has no goal operation; the proof snapshot and every goal come from `lean_session` (Pantograph) | Lean LSP supplies diagnostics and read-only lookups (hover, definition, references, symbols) only. |
| Edit/write diagnostics | Lean LSP diagnostics of the staged source revision | Every diagnostic carries the source hash it belongs to (KNOWN_PROBLEMS K11, stale diagnostics). |
| `coqc` on the target file, `checkpoint` compile | Per-step: LSP diagnostics or `lake env lean <file>` on the staged file. Final: `lake build` of the module | Only the final `lake build` + audit may mark the theorem complete. |
| `coqc` exit code as success in the runner | `lake build` + no `sorry` in the target + `#print axioms` + statement/header audit | One shared definition for the runner and the in-agent final gate (K9). |

## Rules that follow from the decision

1. **The source file stays the authority.** Pantograph states are working copies. A region is solved only after its
   proof text is written to the staged source and the source checks; a Pantograph "no goals" is not a
   certificate on its own (this avoids KNOWN_PROBLEMS K11, solved state vs source).
2. **Goal states must come from the real context.** Start the interactive state from the target theorem as it
   appears in the staged file (its `variable`s, instances, namespaces and preceding `have`s), not from a
   re-typed statement; otherwise the session proves a different goal.
3. **State handles are tied to a source revision.** When the staged source changes, or the Pantograph process
   restarts, old handles are invalid; the session tool must re-open from the source rather than reuse them.
4. **Version pinning.** Pantograph must be built for the same Lean version as the project
   ([`Deliverables/lean-prosa-v06/lean-toolchain`](../../Deliverables/lean-prosa-v06/lean-toolchain):
   `leanprover/lean4:v4.33.1`) and load the same Mathlib/Prosa build. Pin Pantograph **0.3.19** (commit `92d4818`,
   2026-08-29), whose `lean-toolchain` is `v4.33.1`; a mismatched build will not load the project's `.olean` files.
5. **Do not invent command names in prompts.** Name the Pantograph operations in the tool descriptions and prompts
   only after the session tool is implemented, using the exact commands of the pinned Pantograph version
   (`prompt-advices/prompt_revision.md` §0.2).
6. **Passive vs active tools.** Pantograph tactic runs are active proof steps; LSP hover/definition and
   declaration queries are passive lookups (relevant to the stall guards, KNOWN_PROBLEMS K3).

## Implementation answers (checked against Pantograph 0.3.19 source, 2026-10-09)

The open questions of the first version of this note, answered from the Pantograph repository
(`lenianiva/Pantograph`, `doc/repl.md`, `Pantograph/Protocol.lean`, `PantographTest/Integration.lean`).
Nothing has been run yet; the first implementation step is a spike that confirms the items marked *verify*.

- **Version.** Pantograph 0.3.19 (merge commit `92d4818`, 2026-08-29, "Update Lean to v4.33.1") has
  `lean-toolchain` = `leanprover/lean4:v4.33.1`, the package's toolchain. **There is no git tag for it** (tags stop
  at `v0.3.17`), and the commit is on the default branch `dev` (`main` is older), so pinning the commit is the only
  way to get it: `git clone https://github.com/lenianiva/Pantograph && git -C Pantograph checkout 92d4818a4b343d7be293731e03359a19e8082626`.
  Build with `lake build` in that checkout (binary `.lake/build/bin/repl`). Start it from the run copy as
  `lake env <pantograph>/.lake/build/bin/repl <modules>` so that it finds the package's `.olean`s; `<modules>` are
  exactly the modules of the `import` lines of the staged `Solution.lean` (next item). The REPL imports nothing,
  not even `Init`, unless listed.
- **Goal at a proof region.** `frontend.distil` returns, per declaration with `sorry`s, a goal state whose goals
  carry the local context (the `frontend.process` option for collecting `sorry` goals of older releases is gone in
  0.3.19). Two properties of its implementation (`Repl.lean` `frontend_distil` → `Frontend/Distil.lean`
  `distilSearchTargets`) shape how the tool must call it:
  - It takes the file **text** (`file`; there is no path option) and elaborates it against the REPL's
    already-loaded environment from the first character: when an environment is passed,
    `createContextStateFromFile` skips header processing (`Frontend/Basic.lean` L178–179), so `import` lines
    would be read as commands and fail.
  - It **throws on the first command with an error** (`Frontend/Distil.lean` L245–248), so one error anywhere in
    the file means no goal for any region — e.g. while a helper is midway through a broken region.

  The `lean_session` tool therefore prepares the text before every call:
  1. **Header.** Split the staged `Solution.lean` into its `import` header and its body; send only the body. The
     REPL process was started with exactly those imports. When the header changes (the agent may add imports,
     KNOWN_PROBLEMS K1) or a helper module it imports changes (run `lake build <helper>` first), restart the
     process. Positions in Pantograph messages are offset by the header's length; add it back before showing them.
  2. **Broken regions.** In a copy of the body, replace the proof of every region that does not check in the
     current source hash (from the latest diagnostics) by `sorry`, so a broken region cannot hide the goals of
     the others. An error outside the regions (in the skeleton itself) still blocks distillation; report it as a
     diagnostic of the skeleton, not as a backend error.
  3. Call `frontend.distil {"file": <prepared body>, "ignoreValues": false}`, map the returned goals to
     `admit_id`s (see the spike below), and explore sub-goals of a region with `goal.tactic` on its state.
- **Process per workspace, not per session.** Each process loads Mathlib; one process per run copy, shared by the
  prover and lemma sessions of that run (requests are serialised), restarted after a crash, a limit hit, or a
  change of the import header or of an imported helper module. Run
  it under a memory limit (`ulimit -v` or a cgroup): Pantograph's rationale notes that a leaking tactic cannot be
  stopped gracefully. A goal-state handle is valid only for the source hash it was created from (rule 3).
- **Time limits.** `options.set {"timeout": <ms>}` covers all `CoreM` and frontend operations, and tactic strings
  can carry `set_option maxHeartbeats N in …`; both are cooperative, so the tool also keeps a wall-clock limit and
  kills/restarts the process. Any limit hit is a `backend_error` (free under D5).
- **Equivalence checks.** There is no stand-alone `isDefEq` command; `show <P>` on a goal state performs the
  check in that goal's context ([lean_session-equivalence.md](known-problem-fixes/lean_session-equivalence.md)).
- **Error classes.** A reply `{"error": …, "desc": …}` is a backend/command error (tool error, never drift, never
  a retry). A `goal.tactic` reply without a `goals` field is a failed tactic, shown to the agent with its
  `messages` (normal proof feedback).

### First spike (before the `lean_session` tool is written)

On the PC, with the package built and Pantograph `92d4818` built, check with small test files:

1. **Goal order**: a theorem with two `:= (by sorry)` regions; the goals returned by `frontend.distil` come back in
   the order of the `sorry`s (needed to map goals to `admit_id`s, since the result has no positions).
2. **Header**: a body sent without its `import` lines to a REPL started with those imports elaborates; the same
   text with the `import` lines fails (confirms the stripping rule); restart after adding an import works.
3. **Broken region**: a file with one region containing an error yields no targets; after that region's proof is
   replaced by `sorry`, the goals of the other regions come back.
4. **Root goal**: `goal.start {"expr": "<statement>.{u, v}", "levels": ["u", "v"]}` on a real task, then
   `unfold`, then `show <unfolded statement>` succeeds and `show <statement with Type 0>` fails.
5. **Holes**: `show _` and `show ?x` succeed on any goal (why holes are rejected before the check,
   `lean_session-equivalence.md`); the stand-alone elaboration probe described there fails on them. The token
   scanner accepts `Lemma3_05_statement`, `job_cost`, `List.get?`, `fun _ => …` and `Sort ?u.12` (mapped to
   `Sort _`), and rejects `f _ x`, `?x`, `?_` and `sorry`.
6. **Limits**: a deliberately slow `simp`/`decide` under `options.set {"timeout": …}` and `maxHeartbeats`; the
   process memory under one full Mathlib + Prosa import.

## Spike results (run 2026-10-09 on the CityU PC; scripts `leanbuddy/scripts/pantograph-spike/`)

Pantograph `92d4818` (0.3.19) against the built package (task 2005-ECRTS-Lemma3, staged per D14). All checks pass;
two answers above change (marked **changed**).

| # | Check | Result |
|---|---|---|
| 1 | Goal order of `frontend.distil` | **changed**: goals come back in **reverse** source order (trailing goal, then the last region, …, then the first region); same for `cases` branches. Map goals by reversed order and confirm each with `show <region statement>`. |
| 1b | Focusing one goal | `goal.tactic` with `goalId` on a multi-goal `distil` state replaces only that goal; the other regions' goals stay, with their names (`_uniq.N`). A region session tracks "its" goals by name. |
| 2 | Header | confirmed: text with `import` lines fails ("invalid 'import' command"); without them a name from a not-yet-imported module is unknown; after restarting with that import it resolves. |
| 3 | Broken region | confirmed: one error aborts `distil`; masking the region's proof to `(by sorry)` brings all goals back. |
| 4 | Root goal | confirmed: `goal.start {"expr": "<statement>.{u, v}", "levels": ["u","v"]}` + `unfold <statement>` gives the `∀ …` goal (4,582 characters pretty-printed); `show <that pretty-printed text>` re-elaborates and succeeds; the `Type 0` variant is rejected. |
| 5 | Holes | confirmed `show _` and `show ?x` succeed on any goal. **changed**: the stand-alone `expr.echo {"expr": "_", "type": "Prop"}` backstop does **not** fail (it returns a metavariable); the `have _probe : (…) := sorry` probe does fail. The token scanner (`tool/lean-term.ts`) is therefore the primary rule, the `have` probe the backstop. |
| 6 | Limits | `options.set {"timeout": 2000}` interrupts a looping `repeat skip` after 2.1 s ("interrupt"); the default `maxHeartbeats` stops it after 4.8 s. One REPL with the task's imports: 6.7 GB resident (mostly shared memory-mapped `.olean`s), start-up 1.5–3.4 s. |

Final gate (D4) end to end, `check.py` in a fresh verification copy: reference solution **PASS** (7.5 s; axioms
`Classical.choice`, `Quot.sound`, `propext`); `sorry` and an added `axiom` FAIL (forbidden token); `native_decide` FAIL
(non-standard axiom — on Lean 4.33 an auxiliary `<decl>._native.native_decide.ax_…`, not `Lean.ofReduceBool`); a
changed `Statement.lean` FAIL (frozen file).

**Operational rule from the spike:** every Lean/Pantograph process on the shared PC runs in a memory-capped cgroup
(`~/research/leanbuddy-work/capped.sh <MemoryMax> <cmd>`, `systemd-run --scope -p MemoryMax=…`). Without it, Lean
jobs plus Pantograph REPLs next to the fleet runs triggered the kernel OOM killer once (see MIGRATION_LOG).
