# Lean 4 Migration Notes for `coq-project.ts`

**Purpose**: Locate Coq projects, parse load arguments, and support compilation and queries with process execution and temporary scripts.

**1. Project Discovery and Load Paths | Rewrite, Large**

- **Location**: [Line 222: resolve](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-project.ts#L222).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Project marker discovery, [From line 183](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-project.ts#L183):

```ts
    const rocqCandidate = path.join(current, "_RocqProject")
    if (Filesystem.stat(rocqCandidate)) return rocqCandidate
    // Fall back to _CoqProject
    const coqCandidate = path.join(current, "_CoqProject")
    if (Filesystem.stat(coqCandidate)) return coqCandidate
```

- **Current behavior**: Finds `_CoqProject`/`_RocqProject`, parses Coq flags, and supplements Prosa load paths.
- **Recommendation**: Locate `lakefile.lean`/`lakefile.toml` and `lean-toolchain`, and execute within the corresponding Lake environment. Remove Coq `-Q/-R` handling and legacy Prosa path workarounds. Do not parse executable lakefiles as Coq flags text.

**2. Compilation and Query Commands | Rewrite, Large**

- **Location**: [Line 173: coqcCmd](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-project.ts#L173).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Coq compilation entry point, [From line 173](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-project.ts#L173):

```ts
export function coqcCmd(): string[] {
  if (isRocq()) return ["rocq", "c"]
  return ["coqc"]
}
```

Query script execution, [From line 271](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-project.ts#L271):

```ts
  const cmd = coqtopCmd()
  const args = [...cmd, "-batch", ...resolved.flags, ...(extra ?? [])]
  return withTemporaryScript("opencode-coqsession-", code, async (script) => {
    const result = await runProcess([...args, "-l", script], resolved.cwd, options)
```

- **Current behavior**: Selects Coq/Rocq commands based on the executable; `run` executes scripts through coqtop in batch mode.
- **Recommendation**: Provide separate Lean file-validation and query/session entry points using the project's pinned toolchain; replace the flags/preamble contract with Lean project environment, imports, and source context.

**3. Temporary Scripts and Output | Modify, Medium**

- **Location**: [Line 230: withTemporaryScript](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-project.ts#L230).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Temporary script path, [From line 237](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-project.ts#L237):

```ts
  const script = path.join(directory, "input.v")
  try {
    await fs.writeFile(script, code, "utf8")
```

Coq output cleanup, [From line 285](../../../prosabuddy-rocq/packages/opencode/src/tool/coq-project.ts#L285):

```ts
export function cleanOutput(output: string): string {
  return output
    .split("\n")
    .filter((l) => !l.match(/^Welcome to (?:Coq|Rocq|the Rocq Prover)/i) && !l.match(/^(?:Coq|Rocq) </) && l.trim())
    .join("\n")
```

- **Current behavior**: Uses `input.v` for temporary scripts; `cleanOutput` removes Coq welcome messages and prompts.
- **Recommendation**: Generate temporary `.lean` inputs while retaining project imports, namespaces, and local context; replace Coq output cleanup. Changing the extension alone is insufficient.

General process execution, output limits, timeouts, cancellation, and temporary-file cleanup can be retained.
