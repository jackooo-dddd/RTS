# Lean 4 Migration Notes for `coq-check.ts`

**Purpose**: Independently invoke coqc on a specified file and return compilation status, error locations, and output.

**1. Standalone Coq Compilation | Modify or Consolidate and Remove, Large**

- **Location**: [Line 14](../../../prosabuddy-rocq/.opencode/tool/coq-check.ts#L14).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Standalone Coq compilation call, [From line 81](../../../prosabuddy-rocq/.opencode/tool/coq-check.ts#L81):

```ts
    const result = await runCoqc(coqcArgs, projectRoot, timeout)

    // Parse errors
```

Coq error-format parsing, [From line 160](../../../prosabuddy-rocq/.opencode/tool/coq-check.ts#L160):

```ts
function parseCoqErrors(output: string): CoqError[] {
  const errors: CoqError[] = []
  // Coq error format: File "path", line N, characters M-M:
  // or: Error: message
  const regex =
    /File "([^"]+)", line (\d+), characters? (\d+)-?(\d+)?:\s*\n?(Error|Warning):\s*([\s\S]*?)(?=(?:File "|$))/g
```

- **Current behavior**: Independently invokes coqc and handles project discovery, flags, and compiler-error parsing.
- **Recommendation**: Consolidate this capability into the new Lean compilation tool, then remove the old entry point. If retained, rewrite `findProjectRoot`, `parseCoqProject`, `parseCoqErrors`, and `runCoqc` using Lake projects and Lean diagnostics.

**2. File and Parameter Contract | Modify, Small**

- **Location**: [Line 8](../../../prosabuddy-rocq/.opencode/tool/coq-check.ts#L8).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Compilation parameter description, [Line 47](../../../prosabuddy-rocq/.opencode/tool/coq-check.ts#L47):

```ts
        "Extra arguments to pass to coqc, e.g. '-Q . MyLib' or '-R . prosa'"
```

File parameter description, [Line 31](../../../prosabuddy-rocq/.opencode/tool/coq-check.ts#L31):

```ts
      .describe("Absolute or relative path to the .v file to compile"),
```

- **Current behavior**: Parameters and instructions target `.v`, Coq flags, and coqc return values.
- **Recommendation**: Update these according to the retention or consolidation decision; the old entry point must not continue bypassing the new proof-workflow validation.

General process-output packaging can be reused; this tool currently provides a standalone compiler entry point.
