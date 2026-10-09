# Lean 4 Migration Notes for `tool.ts`

**Purpose**: Define the general tool interface, execution context, input validation, and output packaging.

**1. Tool Definitions and Execution Context | Retain, None**

- **Location**: [Line 9](../../../prosabuddy-rocq/packages/opencode/src/tool/tool.ts#L9).

**Source code to retain** (excerpt):

General tool definition interface, [From line 50](../../../prosabuddy-rocq/packages/opencode/src/tool/tool.ts#L50):

```ts
  export function define<Parameters extends z.ZodType, Result extends Metadata>(
    id: string,
    init: Info<Parameters, Result>["init"] | Awaited<ReturnType<Info<Parameters, Result>["init"]>>,
  ): Info<Parameters, Result> {
```

- **Current behavior**: Defines input validation, execution context, output, and truncation wrappers without Coq types or commands.
- **Recommendation**: Reuse directly, keeping Lean-specific parameters in individual tool schemas.

The general tool interface needs no changes for this migration.
