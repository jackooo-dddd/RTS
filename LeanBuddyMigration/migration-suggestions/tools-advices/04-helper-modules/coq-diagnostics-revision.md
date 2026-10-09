# Lean 4 Migration Notes for `coq-diagnostics.ts`

**Purpose**: Parse Coq compiler output to extract errors, warnings, file locations, and the first error.

**1. Coq Text Diagnostic Parsing | Rewrite, Medium**

- **Location**: [Line 18: LOCATION](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-diagnostics.ts#L18).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Coq file-location format, [Line 18](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-diagnostics.ts#L18):

```ts
const LOCATION = /^File "([^"]+)", line (\d+)(?:, characters? \d+-\d+)?:\s*$/
```

Error and warning classification, [From line 30](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-diagnostics.ts#L30):

```ts
      const errorIndex = block.findIndex((line) => /^\s*Error:/.test(line))
      const warningIndex = block.findIndex((line) => /^\s*Warning:/.test(line))
      const severity = errorIndex >= 0 ? "error" : warningIndex >= 0 ? "warning" : undefined
```

- **Current behavior**: Splits output by Coq File/line/characters text locations; `parseCoqCompilerOutput` aggregates stdout/stderr.
- **Recommendation**: Connect diagnostics from the selected Lean backend and convert positions and severity. If retaining CLI text parsing, implement it against actual output from the pinned Lean toolchain rather than reusing the Coq LOCATION regex.

The diagnostic structure containing file, position, message, and severity can remain the interface exposed to callers.
