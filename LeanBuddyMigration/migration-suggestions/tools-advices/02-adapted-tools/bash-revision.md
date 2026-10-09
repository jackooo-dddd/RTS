# Lean 4 Migration Notes for `bash.ts`

**Purpose**: Execute shell commands and intercept compilation calls or transaction-file modifications that bypass dedicated proof tools.

**1. Compilation Calls That Bypass Proof Tools | Modify, Medium**

- **Location**: [Line 80: isCoqCompilerInvocation](../../../prosabuddy-rocq/packages/opencode/src/tool/bash.ts#L80).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Compiler command recognition, [From line 80](../../../prosabuddy-rocq/packages/opencode/src/tool/bash.ts#L80):

```ts
function isCoqCompilerInvocation(words: string[], index: number) {
  const head = commandHead(words[index] ?? "")
  if (head === "coqc" || head === "coqtop") return true
  return head === "rocq" && shellWord(words[index + 1] ?? "") === "c"
}
```

- **Current behavior**: Recognizes `coqc`, `coqtop`, and `rocq c`; `assertNoDirectCoqCompiler` also checks some shell wrapper forms.
- **Recommendation**: Recognize direct Lean compilation/session entry points according to the new tools' responsibilities, such as `lean`, `lake env lean`, and `lake build`; update tool guidance in `DIRECT_COQ_COMPILER_ERROR`.

**2. Transaction File Write Restrictions | Modify, Medium**

- **Location**: [Line 107: assertNoProofTransactionShellMutation](../../../prosabuddy-rocq/packages/opencode/src/tool/bash.ts#L107).

**Source code to adapt** (only the opening lines or key conditions are shown for long blocks):

Coq file and wildcard matching, [From line 122](../../../prosabuddy-rocq/packages/opencode/src/tool/bash.ts#L122):

```ts
  const mentionsTarget = candidates.some((candidate) =>
    new RegExp(`(?:^|[\\s=:/,(]|\\[)${escapeRegExp(candidate)}(?=$|[\\s:;,)\\]])`).test(unquoted),
  ) || (/[*?][^\s]*\.v\b/.test(unquoted) && transaction.file.endsWith(".v"))
```

- **Current behavior**: Uses `.v` paths and wildcards to detect commands that may modify transaction proof files.
- **Recommendation**: Match `.lean` and the actual transaction file; retain redirection/edit-command checks and point guidance to Lean validation tools.

Shell parsing, process execution, and general permission mechanisms can be retained.
