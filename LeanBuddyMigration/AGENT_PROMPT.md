# Task: port ProsaBuddy from Rocq to Lean 4 ("LeanBuddy")

You are porting ProsaBuddy, an opencode-based agent framework that proves Prosa real-time-scheduling theorems in
Rocq, to Lean 4. The Lean version will prove the 24 Lean case studies in `Deliverables/lean-prosa-v06/`. Everything
has already been analysed and decided; your job is to implement it, verify each step, and report. Work carefully:
the notes are detailed but were written without running any Lean code, so verify every claim you rely on.

Repository root: `/Users/shunqiwang/CityuHK/Research/Lean/TranslationProof` (git, branch `main`, remote
`origin` = github.com/jackooo-dddd/RTS). You run on the user's Mac.

## 1. Read first, in this order

1. `LeanBuddyMigration/README.md` — layout, reading order, implementation order.
2. `LeanBuddyMigration/TARGET_ENVIRONMENT.md` — the agent you build, the Lean package, toolchain, run staging (D14).
3. `LeanBuddyMigration/migration-suggestions/DECISIONS.md` — D1–D14, R1–R7, and the two review-fix tables at the
   end. **DECISIONS is the authority**: when a per-file note disagrees with it, DECISIONS wins.
4. `migration-suggestions/KNOWN_PROBLEMS.md` (K1–K11) and `BACKEND_DECISION.md` (Pantograph, incl.
   *Implementation answers* and *First spike*).
5. Then, per file as you translate it: `tools-advices/` (42 modules), `prompt-advices/prompt_revision.md`
   (8 prompts), `skill-advices/` (8 skills), `gap-revisions/` (§1 prompt.ts, §2 system prompts, §3 small files,
   §4 audit backend, §5 runner, §7 tests), and last `known-problem-fixes/` (applied on top of a translated file).
   `GAPS.md` is a record only.

Code links in the notes point into `LeanBuddyMigration/prosabuddy-rocq/` (pure upstream ProsaBuddy `8e1de8c`;
`BASELINE.md` says how it was built). Line numbers refer to that tree.

## 2. What you may and may not touch

- **Write only** in `LeanBuddyMigration/leanbuddy/` (the new app), `LeanBuddyMigration/MIGRATION_LOG.md` (your log),
  scratch/test material outside git (e.g. `~/leanbuddy-work/`), and — only to correct them, with a log entry — the
  notes under `LeanBuddyMigration/migration-suggestions/`.
- **Read-only**: `LeanBuddyMigration/prosabuddy-rocq/` (reference; never run or patch it), `Deliverables/` (the Lean
  package and its frozen benchmark; never build inside it, copy it instead), `replicate-prosa-buddy/` (the Rocq
  replication; its runner shows expected behaviour), `Prosa-Shunqi/`, `RTS_Papers/`.
- `Deliverables/lean-prosa-v06-reference-solutions/` may be used as *positive fixtures for the final-gate tests*
  only. Never copy a reference solution into any workspace the proving agent can read.
- **Do not touch** the CityU PC experiments (the ProsaBuddy fleet under `~/research/RTS/replicate-prosa-buddy/results/`
  and the rocq-proof-ablation runs, also `.claude/worktrees/rocq-proof-ablation` in this repo). Another session
  monitors them.
- **Git**: create branch `leanbuddy-migration` before your first commit; commit at each milestone (§4) with clear
  messages; never commit `node_modules/`, `.lake/`, build outputs, or secrets; **never push without asking**.
- **Secrets**: never print, log or commit API keys, OAuth tokens or passwords. Refer to the model proxy key through
  the existing env/config mechanism only.
- **CityU PC** (only when a phase below says so, and after asking): `ssh cityu-wsl` through the existing SSH
  ControlMaster. If it needs authentication, ask the user to run `ssh -MNf cityu-windows`; never ask for, use or
  store a password. Keep SSH config and strict host-key checking as they are. Do not modify VPN/Clash, disable the
  firewall, expose ports, reboot, or install WSL. Keep all PC files under `~/research/`. The PC copy
  `~/research/RTS/Deliverables/lean-prosa-v06/` contains an extra `Solutions/` folder with reference proofs: never
  stage it.

## 3. Ask the user before

- changing or reinterpreting any decision marked "user decision" (D1–D6, D8–D11), or anything of similar weight
  (backend, tool surface, success criterion, retry accounting, what is dropped);
- if a spike result contradicts BACKEND_DECISION (e.g. Pantograph cannot do something D1 relies on): stop, report
  the evidence and options;
- running the model (any end-to-end run costs tokens), touching the PC, installing anything system-wide, pushing.

Decisions marked "Claude" (R1–R7, D12–D14) you may adjust when the code shows a better way: log the reason and tell
the user in your next report. Small implementation choices: decide, log, move on.

## 4. Plan (phases end in a short report to the user; do not skip verification)

**Phase 0 — workspace.**
Copy `prosabuddy-rocq/` to `LeanBuddyMigration/leanbuddy/` (keep its `.gitignore`; drop `BASELINE.md`, add a short
`README` saying what this tree is). Install dependencies with Bun 1.3.10
(`replicate-prosa-buddy/.tools/bin/bun install` in `leanbuddy/`). Run `bun run typecheck` (root) and
`bun test --timeout 30000` (in `packages/opencode`) **before changing anything**, and record the baseline in
`MIGRATION_LOG.md` (on the PC the pristine 8e1de8c tree had 129 pass / 9 fail, all 9 being 5-second timeouts; your
Mac numbers may differ — what matters is that you know which failures pre-exist). Start `MIGRATION_LOG.md` with a
table of every note file and its status (todo / done / deviated).

**Phase 1 — Lean environment and Pantograph spike (gate for everything else).**
- Make a master copy of `Deliverables/lean-prosa-v06/` outside git (e.g. `~/leanbuddy-work/lean-prosa-v06-master/`),
  then `lake exe cache get` and `lake build` there (toolchain `v4.33.1` is installed in `~/.elan`; never run
  `lake update`). Record build time and `.lake/build` size (it decides the per-run copy cost, D14).
- Build Pantograph at commit `92d4818a4b343d7be293731e03359a19e8082626` (branch `dev`; there is no `v0.3.19` tag)
  in `~/leanbuddy-work/Pantograph`, and run it from a run copy with `lake env …/repl <imports>`.
- Run the six checks of BACKEND_DECISION *First spike* (goal order from `frontend.distil`; header stripping and
  restart; broken region replaced by `sorry`; root goal open/unfold/`show`; hole rejection incl. the token rules in
  `lean_session-equivalence.md`; time/memory limits). Keep the test files and a script that reruns them.
- Also confirm the D4 gate end to end: `benchmark/check.py` PASSES on a reference solution placed into a
  verification copy, and FAILS for `sorry`, an added `axiom`, `native_decide`, a changed `Statement.lean`.
- Write results into BACKEND_DECISION (*Implementation answers* → confirmed / changed). **Report and wait** if any
  check contradicts the notes.

**Phase 2 — tool surface (D2, D6).** Rename tools to `lean_session`, `lean_query`, `lean_check`; keep `checkpoint`,
`proof_plan`, `lsp` (reduced, D3). Update every string list that names tools (guards, passive/active classification,
caches, prune lists, permissions). Delete what D6 drops. Typecheck.

**Phase 3 — final gate (gap-revisions §4, D4, K9).** `tool/lean-gate.ts` replacing the OCaml/AST audit; one
function used by `checkpoint`, `task` and (later) the runner. Port its tests (§7) with the Phase 1 fixtures.

**Phase 4 — `lean_session` / `lean_query` / `lean_check` on Pantograph (BACKEND_DECISION, D1–D3, D10, D14).**
One Pantograph process per run copy, header handling, broken-region masking, goal-state handles tied to the source
hash, the statement-equivalence service (`known-problem-fixes/lean_session-equivalence.md`, incl. root goal and
hole rules), limits and error classes (backend errors are free under D5). Integration tests behind an env flag.

**Phase 5 — the rest of the app.** `session/prompt.ts` (gap-revisions §1), system prompts (§2), small files (§3),
the per-file `tools-advices/` notes, prompts (`prompt_revision.md`), skills (`skill-advices/`), then
`known-problem-fixes/` (K2 amendments, K4 `no_ready_region`, K5 plan keyed by file+theorem, K6/K7 elaboration and
plan-owned `kind`/`layer` with the D10 field lists, K8, K10 `limit.context`, S25, S26), D13 evidence prefixes.
Port each module's tests together with the module (gap-revisions §7 and the extra tests listed in
`known-problem-fixes/README.md`).

**Phase 6 — consistency sweep.** The model must never see Rocq vocabulary (D2 rule). Check e.g.
`grep -rniE "coq|rocq|petanque|ssreflect|mathcomp|admitted|qed\b|\.v\b" leanbuddy/packages/opencode/src leanbuddy/.opencode`
and justify every remaining hit (identifiers in comments are fine; prompts, tool descriptions, reminders and
permission lists are not). Typecheck clean; tests: no new failures versus the Phase 0 baseline.

**Phase 7 — smoke run (ask first).** One case study, locally, through `opencode run` with the Lean agent, to see
that the whole loop works (plan → skeleton → regions → `lean_session` → gate). A proof is not required; crashes,
Rocq strings, wrong tool names, or gate/staging errors are what you are looking for. Ask the user which model
endpoint to use (the replication used `gpt-6-luna`, effort `xhigh`, via CLIProxyAPI on the PC).

**Phase 8 — benchmark runner (last, ask first).** gap-revisions §5 (staging per D14, success = D4 in a fresh
verification copy, retry accounting per D5, `lsp` allowed, edit/write denies), then deployment to the PC under
`~/research/RTS/leanbuddy/` following §2's PC rules.

## 5. How to work

- Translate by editing the copied tree, not by rewriting from scratch: most of opencode is language-independent.
  About 63 of the 325 source files under `packages/opencode/src` mention Rocq/Coq (those files total ≈32k lines, most of it generic); the notes cover them.
- For each file: read the note(s), read the code at the cited lines, change it, run its tests, tick it off in
  `MIGRATION_LOG.md`. If a note is wrong or outdated (line numbers drift, a claim does not hold), fix the code
  correctly, correct the note, and log both.
- Verify Lean/Pantograph behaviour by running it, not from memory; cite the source file and line when you rely on
  Pantograph internals.
- Keep changes reviewable: one concern per commit, messages that say which decision/note they implement.
- Reports to the user: what was done, what was verified (with numbers), what deviated from the notes and why, what
  needs a decision. Be plain and concise; do not claim something works unless you ran it.

## 6. Done means

- `leanbuddy/` typechecks; unit tests pass except the failures recorded in the Phase 0 baseline; integration tests
  for the gate and `lean_session` pass against the built package.
- The spike results and every deviation are recorded (BACKEND_DECISION, `MIGRATION_LOG.md`).
- No Rocq vocabulary reaches the model; every note in `migration-suggestions/` is marked done or deviated.
- Phases 7–8 only as far as the user approved.
