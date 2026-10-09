# Revision: `session/prompt.ts` (runtime controller)

**File**: [`packages/opencode/src/session/prompt.ts`](../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts) (3,364 lines, baseline 8e1de8c).
**Purpose**: per-turn controller. It binds the proof file, injects runtime reminders, gates tools, stops turns, and
builds the lemma/finalization prompts. **Change size**: Modify, Large (84 Rocq-specific lines; logic kept).
**Follows**: DECISIONS D2 (tool names), D3 (LSP), D4 (final gate), D5 (stops are free), R1–R3, R7.

Abbreviation: `L` = `../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts`.

---

**1. Proof-file detection (`.v` → `.lean`, target = `Solution.lean`) | Modify, Small**

- **Location**: [L#L211](../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L211), [L#L278-L280](../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L278), [L#L368](../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L368), [L#L466](../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L466), [L#L690-L716](../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L690).

```ts
    if (!binding?.file.endsWith(".v") || !(await Filesystem.exists(binding.file))) return
      for (const match of part.text.matchAll(/\bcoqc\s+([A-Za-z0-9_./-]+\.v)\b/gi)) candidates.add(match[1])
          if (part.type === "file" && part.filename?.endsWith(".v")) {
```

- **Current behavior**: a session is a proof session only for `.v` files; the target is inferred from "target file `X.v`" or "`coqc X.v`" in the prompt or from an attached `.v`.
- **Change**: introduce one helper `isProofSourceFile(path)` = `path.endsWith(".lean")` and use it at all five places. Prompt inference: match "target file `X.lean`" and "`lake env lean X.lean`" / "`lean_check X.lean`". In the benchmark the target is always `CaseStudies/<G>/<F>/Solution.lean`; `Statement.lean` must never be bound as the proof file (it is read-only, D4).

**2. Prover finalization reminder (no terminator in Lean) | Rewrite, Small**

- **Location**: [L#L366-L392](../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L366).

```ts
      "The theorem-level terminator and any `Admitted.` -> `Qed.` conversion are prover-owned, because they are outside every lemma editable region.",
      "Change the theorem terminator to `Qed.` only after the complete theorem body has no remaining goals, admits, or aborts and validates with Coq.",
```

- **Change** (R2): replace both lines with: "Theorem closure is prover-owned: the `solution` body is complete only when no `sorry` remains outside and inside the regions and the final gate (frozen statement check, `lake build`, `#print axioms`) passes." Keep "do not dispatch a final lemma task" and "do not edit inside solved regions". `final_theorem_gate.reason` must come from the D4 gate.

**3. Lookup / active-step classification (tool names) | Modify, Medium**

- **Location**: `hasCompletedTargetedSemanticInspection` [L#L458-L486](../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L458), `isWholeLemmaPassiveLookupPart` [L#L511-L527](../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L511), `isWholeLemmaActiveProofAttemptPart` [L#L529-L550](../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L529), startup lookup [L#L1584-L1589](../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L1584).

```ts
        if (part.tool === "coqtop") {
          const command = toolInputString(part.state.input, "command")
          if (["check", "search", "print"].includes(command)) return true
        if (part.tool === "coq_session") {
          if (toolInputString(part.state.input, "op") !== "step") return false
```

- **Change** (D2, D3): one shared classification table used by `prompt.ts` and `proof-workflow.ts` (`fallbackLookupActivity`, `isFallbackPassiveLookupPart`):

  | Tool / operation | Class |
  |---|---|
  | `read`, `grep`, `glob`, `lsp` (all operations) | passive |
  | `lean_query` (all) | passive |
  | `lean_session` open / goals / inspect | passive (inspection) |
  | `lean_session` tactic run that changed the goal state | active |
  | `edit`/`multiedit`/`write`/`apply_patch` on the target | active |
  | `lean_check`, `checkpoint` | validation (neither) |

  Remove the `coqtop`, `coq_session`, `petanque` branches. A `read` of another `.lean` file counts as targeted semantic inspection (was `.v`, L466).

**4. Accepted-plan hard tool gate | Modify, Small**

- **Location**: [L#L79-L94](../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L79), applied at [L#L128](../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L128).

```ts
  const ACCEPTED_PLAN_HARD_BLOCKED_TOOLS = [
    "read", "grep", "glob", "lsp", "coqtop", "codesearch", "list", "bash", "batch", "task", "skill", "proof_plan",
    "coq-proof-dag", "pdf-read",
```

- **Change**: `coqtop` → `lean_query`; delete `coq-proof-dag` and `pdf-read` (removed, D6).

**5. Recovery reminder after a transaction restore | Modify, Small**

- **Location**: [L#L1250-L1264](../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L1250).
- **Change**: "read/edit/…/checkpoint/coqc" → "…/checkpoint/lean_check"; "Coq-session use" → "`lean_session` use"; "read the target .v file" → "read the target `Solution.lean`"; "theorem terminator remains, edit only that terminator" → "only the final `sorry`-free closure remains; finish the parent composition and run the final checkpoint"; "compiler-backed checkpoint/coqc receipt" → "checkpoint/`lean_check` receipt".

**6. `proof.tex` gate | Keep, wording only**

- **Location**: [L#L587-L590](../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L587), [L#L1619-L1662](../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L1619).
- **Change** (R3): logic unchanged. Text: "current Coq proof file" → "current Lean proof file"; "before editing Coq" (L1757) → "before editing the Lean proof". `proof.tex` is found next to `Solution.lean` in each case-study folder; `findUp` from the bound file works unchanged.

**7. Scaffold, first-attempt and lookup-streak reminders | Modify, Small**

- **Location**: [L#L1674](../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L1674), [L#L1696-L1698](../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L1696), [L#L1737](../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L1737), [L#L1946](../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L1946), [L#L1976-L1990](../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L1976).
- **Change**:
  - `coq_session`/`petanque` step → `lean_session` tactic run; `coqtop Check/Search/Print` → `lean_query`; "Prosa/MathComp declaration" → "Prosa/Mathlib declaration".
  - "Temporary admits are permitted only inside the accepted first-level proof regions" → "Temporary `sorry` placeholders are permitted only inside accepted `:= (by …)` regions" (R1).
  - "use LSP diagnostics, `coq_session`…" → "use the diagnostics attached to the edit result or `lean_session`"; L1946 list: `grep`, `glob`, `lean_session`, `lsp` (read-only lookups, D3), `lean_query`.

**8. Turn stops: make them free and machine-readable | Modify, Medium**

- **Location**: `stalled_wide_fallback` text [L#L1210](../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L1210); livelock / passive-lookup stop [L#L1502-L1565](../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L1502).
- **Current behavior**: the controller ends the turn with a text message; the runner cannot tell it from a failed attempt and charges a retry (KNOWN_PROBLEMS K3).
- **Change** (D5): every controller stop also writes a structured record (`{"controller_stop": "<reason>", "required_action": "...", "admit_id": "..."}`) to the session's message metadata so the runner can recognise it and start a free recovery. Keep the reasons; make `required_action` something the model can do — when the reason is a missing bridge, the required action is a plan amendment (KNOWN_PROBLEMS K2), not "make a theorem-level edit" against a locked plan.

**9. Direct-probe / whole-lemma mode | Keep, wording only (R7)**

- **Location**: [L#L312-L321](../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L312), whole-lemma reminders [L#L1928-L1992](../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L1928).
- **Change**: tool names per D2; "search … in the current workspace and prosa/" → "… and `Prosa/`" (Lean package layout). Unused in the replication; port last.

**10. Live proof snapshot for proof agents | Modify, Small**

- **Location**: `proofAgents` refresh [L#L205](../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L205), injection [L#L2693](../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L2693).
- **Change**: the snapshot shown to the agent comes from the `lean_session` goal state of the active region (Pantograph); LSP diagnostics are attached as a separate, revision-tagged block. There is no LSP goal operation to inject (D3); the source file stays the authority (BACKEND_DECISION rule 1).

**Retained unchanged**: transaction recovery logic, cache-projection options, lemma continuation and scheduling, the
passive-lookup counters' thresholds (re-tune after the first Lean runs), and the whole message/loop machinery.
