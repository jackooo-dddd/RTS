# Lean 4 Migration Notes for `coqtop.ts`

**Purpose**: Query lemmas, definitions, and types through Coq commands and execute temporary query scripts.

**Decided 2026-10-09 (DECISIONS D2):** the Lean tool is named `lean_query` (read-only `#check`/`#print`/name search in the target's context).

**1. Query Command Generation | Rewrite, Large**

- **Location**: [Line 44](../../../prosabuddy-rocq/packages/opencode/src/tool/coqtop.ts#L44).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Query command generation, [From line 44](../../../prosabuddy-rocq/packages/opencode/src/tool/coqtop.ts#L44):

```ts
    switch (params.command) {
      case "check":
        script.push(`Check ${params.input}.`)
        break
      case "search":
        script.push(`Search ${params.input}.`)
        break
      case "print":
        script.push(`Print ${params.input}.`)
```

- **Current behavior**: Generates `Check`, `Search`, `Print`, and `Show.` for check/search/print/state; eval accepts Coq code directly.
- **Recommendation**: Connect check/print to Lean `#check`/`#print` or equivalent type queries; reimplement search using available Lean/Mathlib query capabilities. Read Lean goals for state and distinguish term evaluation from command execution for eval; renaming commands alone is insufficient.

**2. Execution Environment and Style Checks | Modify, Medium**

- **Location**: [Line 32](../../../prosabuddy-rocq/packages/opencode/src/tool/coqtop.ts#L32).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Coq style checks, [From line 32](../../../prosabuddy-rocq/packages/opencode/src/tool/coqtop.ts#L32):

```ts
    if (params.command === "eval" || params.command === "state") {
      assertNoRewriteBang(params.input, `coqtop ${params.command} input`)
      assertNoIntuition(params.input, `coqtop ${params.command} input`)
    }
```

Coq query backend, [Line 70](../../../prosabuddy-rocq/packages/opencode/src/tool/coqtop.ts#L70):

```ts
    const { exit, stdout, stderr } = await CoqProject.run(code, projectInput, extraFlags, { signal: ctx.abort })
```

- **Current behavior**: state/eval invoke Coq style guards, pass query scripts to `CoqProject.run`, and clean Coq output.
- **Recommendation**: Connect a Lean query backend with project imports/options; remove SSReflect guards, Coq flags, and prompt parsing.

**3. Corresponding Description File | Modify, Small**

- **Location**: [coqtop.txt](../../../prosabuddy-rocq/packages/opencode/src/tool/coqtop.txt#L1).

**Description text to update** (excerpt):

Coq query command descriptions, [From line 5](../../../prosabuddy-rocq/packages/opencode/src/tool/coqtop.txt#L5):

```text
Available commands:
- "check <term>": Check the type of a term
- "search <pattern>": Search for lemmas matching a pattern
- "print <name>": Print the definition or type of a named entity
- "state": Get the current proof state (goals, hypotheses, context)
- "eval <coq_code>": Evaluate a Coq command and return the result
```

- **Current behavior**: Describes Coq queries, `state/eval`, and SSReflect restrictions.
- **Recommendation**: Document Lean usage according to the implemented query capabilities; do not promise Coq Search-equivalent behavior through renaming alone.

Query dispatch, output packaging, and cancellation can be retained.
