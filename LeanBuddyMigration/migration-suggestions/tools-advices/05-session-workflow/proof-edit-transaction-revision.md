# Lean 4 Migration Notes for `proof-edit-transaction.ts`

**Purpose**: Manage staging, revisions, authorized scopes, conflict recovery, and commit status for proof edits.

**1. Theorem Range Discovery | Rewrite, Large**

- **Location**: [Line 550: theoremBoundary](../../../prosabuddy-rocq/packages/opencode/src/session/proof-edit-transaction.ts#L550).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Coq theorem declaration matching, [From line 555](../../../prosabuddy-rocq/packages/opencode/src/session/proof-edit-transaction.ts#L555):

```ts
    const declaration = new RegExp(
      `\\b(?:Lemma|Theorem|Corollary|Proposition|Fact|Remark|Example)\\s+${escapeRegExp(theorem)}\\b`,
      "g",
    )
```

Proof entry-point recognition, [From line 570](../../../prosabuddy-rocq/packages/opencode/src/session/proof-edit-transaction.ts#L570):

```ts
    const proofs = [...theoremText.matchAll(/\bProof\s*\./g)]
    if (proofs.length !== 1) {
      throw new Error(
        `proof_transaction_structure_rejection: theorem ${theorem} must contain exactly one explicit Proof command`,
```

- **Current behavior**: Masks Coq comments/strings, then matches theorem, Proof, and terminators to establish theorem-level editing boundaries.
- **Recommendation**: Use Lean syntax ranges to protect declaration headers and locate proof bodies; support tactic and term proofs while retaining prefix/suffix text consistency checks.

**2. Proof-Fragment Validity | Rewrite, Medium**

- **Location**: [Line 591: assertProofSegment](../../../prosabuddy-rocq/packages/opencode/src/session/proof-edit-transaction.ts#L591).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Coq terminator checks, [From line 608](../../../prosabuddy-rocq/packages/opencode/src/session/proof-edit-transaction.ts#L608):

```ts
    const terminators = [...maskedSegment.matchAll(/\b(?:Qed|Defined|Admitted|Abort)\s*\./g)]
    if (terminators.length !== 1) {
      throw new Error("proof_transaction_structure_rejection: staged theorem body must contain exactly one terminator")
    }
```

- **Current behavior**: Rejects copied Proof/End commands and checks Coq terminator counts; `assertAuthorized` uses these boundaries to reject out-of-scope edits.
- **Recommendation**: Check Lean declaration/proof ranges and indentation scope instead of counting Qed/Admitted. Explicit region markers can remain, with their syntax kept consistent with workflow.

**3. Transaction Creation Conditions | Modify, Small**

- **Location**: [Line 1066: begin](../../../prosabuddy-rocq/packages/opencode/src/session/proof-edit-transaction.ts#L1066).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Creating transactions only for Coq files, [From line 1076](../../../prosabuddy-rocq/packages/opencode/src/session/proof-edit-transaction.ts#L1076):

```ts
    if (!file.endsWith(".v")) return undefined
    const recovered = restore({ ...input, file })
    if (recovered) {
```

- **Current behavior**: Creates proof transactions only for `.v`; errors from `assertPatchTargets` and related functions refer to Coq files.
- **Recommendation**: Switch to `.lean` and update guidance. Ensure proof edits after migration do not bypass staging and write directly to disk because the extension check was left unchanged.

Transaction revisions, locks, staged source, conflict recovery, commits, and persistence can be retained.
