# Lean 4 Migration Notes for `proof-workflow.ts`

**Purpose**: Manage proof regions, subgoal delegation, dependency scheduling, validation certificates, proof progress, and final completion.

**1. Theorem and Proof-Body Boundaries | Rewrite, Large**

- **Location**: [Line 732: theoremSpans](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L732).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Theorem name recognition, [Line 516](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L516):

```ts
  const THEOREM_NAME = /\b(?:Lemma|Theorem|Corollary|Proposition|Fact|Remark|Example)\s+([A-Za-z0-9_']+)/g
```

Proof start/end detection in theoremSpans, [From line 742](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L742):

```ts
      const proof = /\bProof\s*\./g.exec(theoremText)
      const proofStart = proof ? declaration.start + proof.index + proof[0].length : undefined
      const terminator = proofStart === undefined
        ? undefined
        : /\b(?:Qed|Defined|Admitted|Abort)\s*\./g.exec(masked.slice(proofStart, end))
```

- **Current behavior**: `maskCoqCommentsAndStrings`, `theoremRootGoal`, `theoremSpans`, and `deriveBoundProofScope` divide ranges using Coq declarations, Proof, and terminators.
- **Recommendation**: Use Lean syntax ranges to distinguish declaration headers, proof terms, and local blocks, covering `:= by` and term proofs. Parameters, namespaces, and local instances are context to protect. Update `.v` entry checks such as `assertBoundProofBodyMutationAllowed` to `.lean` together.

**2. Region Markers and Local Target Contracts | Rewrite, Large**

- **Location**: [Line 1668: parseRegions](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L1668).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Region-marker comment syntax, [From line 514](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L514):

```ts
  const REGION_BEGIN = /\(\*\s*proof_region\s+begin\s+([\s\S]*?)\s*\*\)/g
  const REGION_END = /\(\*\s*proof_region\s+end(?:\s+admit_id:\s*([^\s*]+))?\s*\*\)/g
```

Empty proof-block recognition, [From line 519](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L519):

```ts
  const EMPTY_PROOF_BLOCK = /\{\s*(?:\(\*[\s\S]*?\*\)\s*)*\}/
  const EMPTY_PROOF_BLOCK_GLOBAL = /\{\s*(?:\(\*[\s\S]*?\*\)\s*)*\}/g
```

Opening lines of targetDeclarations, [From line 1575](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L1575):

```ts
  function targetDeclarations(blockText: string) {
    const masked = maskCoqCommentsAndStrings(blockText) ?? blockText
    const lines = blockText.split("\n")
    const maskedLines = masked.split("\n")
    const declarations: { name: string; statement: string; proposition: string }[] = []
    const declaration = /\b(?:have|suff(?:ices)?|enough)\s+([A-Za-z_][A-Za-z0-9_']*)\b|\bassert\s*\(\s*([A-Za-z_][A-Za-z0-9_']*)\b/
```

Entry condition in localStatementBefore, [From line 3652](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L3652):

```ts
  function localStatementBefore(source: string, headerStart: number) {
    const end = skipIgnoredBackward(source, headerStart)
    if (end <= 0 || source[end - 1] !== ".") return undefined
```

- **Current behavior**: `REGION_BEGIN` uses Coq comments; `targetDeclarations` and related location functions recognize have/assert and similar constructs, treating empty braces as gaps.
- **Recommendation**: Retain marker ID/ownership/dependency semantics while switching to Lean comments; locate targets using Lean local declarations and proof ranges rather than treating braces as proof blocks. Update syntax handling in `parseContractAttributes`, `localStatementBefore`, and `goalFromStatement` together.

**3. Temporary Scaffolds and Prefix Compilation | Rewrite, Large**

- **Location**: [Line 1052: checkpointScaffold](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L1052).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Compilation command in checkpointScaffold, [From line 1096](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L1096):

```ts
    const resolved = await CoqProject.resolve(file)
    const args = [...CoqProject.coqcCmd(), ...resolved.flags, file]
    const timeoutMs = validationTimeoutMs()
    let result: CoqProject.ProcessResult
```

Temporary-file and artifact-cleanup setup in checkpointSourceAs, [From line 1181](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L1181):

```ts
    const directory = path.dirname(file)
    const basename = `OpencodePrefix_${hashText(file + "\n" + source).slice(0, 12)}.v`
    const tempFile = path.join(directory, basename)
    const cleanup = [
      tempFile,
      tempFile.replace(/\.v$/, ".vo"),
```

Opening placeholder generation in maskEmptyProofBlock, [From line 1156](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L1156):

```ts
  function maskEmptyProofBlock(match: string) {
    const close = match.lastIndexOf("}")
    if (close < 0) return match
    if (!match.includes("\n")) return "{ admit. }"
```

- **Current behavior**: `checkpointScaffold`/`checkpointSourceAs` use coqc and temporary `.v` files; `maskEmptyProofBlocksAfter` inserts probe placeholders into later empty blocks.
- **Recommendation**: Validate the corresponding staged Lean source in the Lake environment. If temporary probes use sorry, record its locations and dependencies; results depending on those placeholders must not be certified as completed proofs. Retain the caller-facing `Validation` interface.

**4. Basis for Local Proof Certificates | Rewrite, Large**

- **Location**: [Line 4871: recordCompilerResult](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L4871).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Local-certificate filtering in recordCompilerResult, [From line 5080](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L5080):

```ts
    const prefixCertifiedBlocks =
      !mappedBlock && diagnosticFileMatches(file, input.first_error_file) && input.first_error_line !== undefined
        ? parsed.filter((block) => !block.pending && block.endLine < input.first_error_line!)
        : []
```

Position-based progress check in compilerReachedPastRegion, [From line 4831](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L4831):

```ts
    const end = item.region_end_line ?? item.end_line
    return result.first_error_line > end
```

- **Current behavior**: Based on Coq's sequential compilation and the first error location, regions before the error with no pending gaps can be marked prefix-certified; `compilerReachedPastRegion` provides another check.
- **Recommendation**: The Lean backend must provide evidence that the region finished elaboration and has acceptable proof dependencies. Do not directly reuse the inference that an error later in the file means earlier regions are proved. Certificates should remain bound to the source version and region.

**5. Final Completion and Progress Metrics | Rewrite, Large**

- **Location**: [Line 3939: finalTheoremGate](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L3939).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Terminator check in finalTheoremGate, [From line 3955](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L3955):

```ts
    const terminators = [...masked.matchAll(/\b(Qed|Admitted|Abort)\./g)]
    const final = terminators.at(-1)?.[1]
    if (final !== "Qed") {
```

Gap counting in proofProgressMetrics, [From line 4017](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L4017):

```ts
    const admitCount = countMatches(masked, PENDING_PLACEHOLDER_GLOBAL)
    const emptyBlockCount = countMatches(masked, EMPTY_PROOF_BLOCK_GLOBAL)
    const admittedTerminatorCount = countMatches(masked, /\bAdmitted\./g)
    const abortTerminatorCount = countMatches(masked, /\bAbort\./g)
    const terminators = [...masked.matchAll(/\b(Qed|Admitted|Abort)\./g)]
    const finalTerminator = terminators.at(-1)?.[1]
    const unfinishedCount = admitCount + emptyBlockCount + admittedTerminatorCount + abortTerminatorCount
```

Qed distance in proofProgressMetrics, [Line 4055](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L4055):

```ts
      qed_distance: finalTerminator === "Qed" ? (unfinishedCount === 0 ? 0 : 1) : 2,
```

Coq error matching in expectedIncompleteQedScaffold, [Line 4841](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L4841):

```ts
      !/attempt to save an incomplete proof/i.test(result.message ?? "")
```

- **Current behavior**: Final checks inspect Qed and unfinished markers; `proofProgressMetrics` contains qed_distance/final_qed, while `expectedIncompleteQedScaffold` handles Coq's incomplete-Qed error specially.
- **Recommendation**: Require successful construction of the Lean target declaration with no unfinished-proof dependencies; remove Qed-specific distance/error branches and count gaps using Lean syntax and sorry information. Retain the distinction between local progress and final completion.

**6. Semantic Layers, Candidates, and Target Normalization | Modify, Medium**

- **Location**: [Line 3679: normalizeTargetShape](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L3679).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Lemma-ready layer enum, [Line 3677](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L3677):

```ts
  const LEMMA_READY_LAYERS = new Set(["semantic", "shape", "prosa", "mathcomp", "coq_shape", "local_arithmetic"])
```

Handling in normalizeTargetShape that changes Lean binders and names, [From line 3690](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L3690):

```ts
      .replace(/[{}]/g, " ")
      .replace(/[()]/g, " ")
      .replace(/\s+/g, " ")
      .trim()
      .toLowerCase()
```

MathComp candidate fields in parseRegions, [From line 1733](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L1733):

```ts
      const mathcompCandidateLemmas = attrList(
        attrValue(attrs, contractAttrs, "mathcomp", "mathcomp_candidates", "mathcomp_candidate_lemmas"),
      )
```

- **Current behavior**: Contract/target handling uses Coq text rules; related layers and candidate fields include coq_shape, mathcomp, and `mathcomp_candidate_lemmas`.
- **Recommendation**: Use Lean target representations and Mathlib fields, preserving binders, Unicode names, Bool/Prop distinctions, and instance-parameter differences; update `parseRegions`, lemma-ready checks, and `recordVerifiedRouteFailure` together.

**7. Tool Recognition and Proof-Task Entry Points | Modify, Medium**

- **Location**: [Line 6116: isFallbackPassiveLookupPart](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L6116).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Coq query branch in isFallbackPassiveLookupPart, [From line 6119](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L6119):

```ts
    if (part.tool === "coqtop") {
      const command = toolInputString(part.state.input, "command")
      return ["search", "check", "print", "eval"].includes(command)
    }
```

Coq session branch in isFallbackPassiveLookupPart, [From line 6123](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L6123):

```ts
    if (part.tool === "coq_session") {
      const op = toolInputString(part.state.input, "op")
      return op === "open" || op === "goal" || op === "inspect"
    }
```

Compiler-tool check in isFallbackActivePart, [From line 6141](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L6141):

```ts
    if (
      (part.tool === "edit" || part.tool === "write" || part.tool === "coqc" || part.tool === "checkpoint") &&
      (!targetFile || toolInputTouchesFile(part.state.input, targetFile))
    ) {
```

Opening file-type check in assertProofTaskDispatchAllowed, [From line 6705](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L6705):

```ts
    const binding = SessionProof.get(input.sessionID)
    const previous = get(input.sessionID)
    const file = binding?.file ?? previous?.file
    if (!file || !file.endsWith(".v") || !(await Filesystem.exists(file))) {
      return {
        active: false,
        decision: "allowed_without_bound_proof_workflow",
        reason: "no live Rocq proof workflow is bound to this task session",
```

- **Current behavior**: Lookup/progress tracking recognizes coqtop/coq_session/coqc; `assertProofTaskDispatchAllowed`, `planNextSubtask`, source mutation, and edit guards contain `.v` branches.
- **Recommendation**: Consistently update actual Lean tool IDs and file checks so calls still enter the existing workflow; retain general dispatch and dependency-readiness rules.

DAG scheduling, region ownership, delegation states, revision budgets, and the progress-recording framework can be retained.

**8. Contract Parser for Region Markers and Contract Comments (new in upstream 8e1de8c) | Rewrite, Medium**

- **Location**: [Line 1356: parseAttributes](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L1356), [Line 1484: attrList](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L1484), field sets [REGION_MARKER_FIELDS, line 1529](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L1529) and [CONTRACT_FIELDS, line 1400](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L1400), version stamp [CONTRACT_PARSER_VERSION, line 44](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L44) checked at [line 2012](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L2012) and [line 3268](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L3268).

**Source code to adapt**:

Only known field names start a new `key: value`; brackets and quotes are respected, [From line 1358](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L1358):

```ts
    const fields = new Set([...REGION_MARKER_FIELDS, ...CONTRACT_FIELDS, "informal proof"])
    ...
      if ("([{".includes(char)) depth++
      else if (")]}".includes(char)) depth = Math.max(0, depth - 1)
      if (depth || (index > 0 && !/[\s;]/.test(text[index - 1]))) continue
```

- **Current behavior**: Replaces the old regex reader, which cut values at whitespace or `*` (so `normal_form: #|alpha' tsk| * (R - c + 1)` was truncated and every review reported a false "target normal form differs", and `depends_on: [a, b]` produced entries `[a` / `b]`). Values now run to the next known field; a value of `prosa:`/`mathcomp:` inside `evidence` does not start a new field; `depends_on` accepts JSON string lists and legacy `[a,b]`; `none` / `(none)` mean empty. Stored materialization reviews carry `parser_version`, and reviews made by an older parser are re-run instead of trusted. Several consecutive contract comments after a begin marker are merged.
- **Recommendation**: Lean contracts will live in Lean comments (`/- … -/` or `--`), and Lean terms contain `:` (type ascriptions), `|`, `⟨⟩`, `fun x =>`, `∀` and `∑ i ∈ s, …`. Keep the design (closed field list, nesting- and quote-aware scan, version stamp) and extend the nesting set to `⟨⟩` and `⦃⦄`; make sure a type ascription such as `(x : Job)` inside `normal_form` cannot be read as a new field (it is protected only by the "known field name" rule and the bracket depth). Keep the parser version in persisted reviews so a parser change invalidates old reviews.
- **Field sets after D10/D13 (decided)**: required marker fields `owner`, `admit_id`, `theorem`, `target`, `plan_node`; required contract fields `plan_node`, `depends_on`, `source`, `input`, `output`, `expected`, `normal_form`, `evidence`. `kind` and `layer` leave both required sets but stay in the *recognized* set, so a `kind:` or `layer:` written out of habit still ends the preceding value; the value is dropped with one warning in the review and never compared with the plan (that comparison was the K7 label drift). Evidence prefixes: `prosa:`, `mathlib:`, `local:`, `context:`, `lean:`, `compiler:` (D13); `mathcomp:`/`coq:` give a warning, not a block. Bump `CONTRACT_PARSER_VERSION` for the Lean parser.

**9. Lookup Guard and Bounded Parent Repair (changed in upstream 8e1de8c) | Modify, Small**

- **Location**: limits at [lines 526-529](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L526), [Line 6155: fallbackLookupActivity](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L6155), [line 7024](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L7024), [line 7248](../../../prosabuddy-rocq/packages/opencode/src/session/proof-workflow.ts#L7248); runtime side in [prompt.ts line 78](../../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L78) and the reminder at [prompt.ts line 1331](../../../prosabuddy-rocq/packages/opencode/src/session/prompt.ts#L1331).
- **Current behavior**: 5 passive lookups (read/grep/glob/lsp) without a proof edit now only inject a `<proof-lookup-progress-reminder>`; the turn is stopped only after 20 lookups of which at least 5 are identical query/output pairs. A parent that takes over a stuck child region gets at most 8 tool actions. Separately, a prover with an accepted plan is stopped after 20 passive lookups with no edit, active proof step or new certificate (`passive_lookup_stagnation`, reported through the same `materialization_livelock` message).
- **Recommendation**: Classify the Lean tools (`#check`/`#print` queries, Loogle/LeanSearch-style search, LSP hover/definition) as passive or active explicitly; a Lean `exact?`/`apply?` call is an active proof step, not a lookup. See KNOWN_PROBLEMS K3: every stop of this kind costs the benchmark runner a retry.
