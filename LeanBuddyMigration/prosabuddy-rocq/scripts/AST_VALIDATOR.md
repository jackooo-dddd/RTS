# Rocq classified-AST validator

This directory contains two parts:

- `classify_vernac_ast.ml` annotates every `coq-lsp` astdump command with
  Rocq's `Vernac_classifier.classify_vernac` result and retains the original
  AST.
- `validate_classified_ast.py` compares an original and a candidate classified
  AST and emits an acceptance/rejection verdict with machine-readable reasons.

The validator implements the following strict policy:

1. Exactly one target proof may change.
2. The target theorem declaration must be AST-identical to the original after
   source locations are removed.
3. Every command outside the target proof must remain AST-identical and in the
   same order, except explicitly allowlisted `VernacRequire` insertions.
4. In the target proof, a `VernacSynterp` command must be a trusted
   `VernacExtend` classified as `ProofStep`.
5. In the target proof, a `VernacSynPure` command must be classified as
   `ProofStep`.
6. The only accepted closing command is an unnamed opaque `Qed.`
7. Unknown schema, classifier errors, controls, attributes, extensions, and
   classifications are rejected by default.

## Generate and classify AST files

Generate raw JSONL AST dumps with the installed coq-lsp astdump plugin:

```bash
fcc --no_vo --plugin=coq-lsp.plugin.astdump original.v candidate.v
```

This creates files such as:

```text
original.v.jsonl.astdump
candidate.v.jsonl.astdump
```

Build the classifier helper:

```bash
scripts/build_classify_vernac_ast.sh
```

Classify both dumps:

```bash
scripts/classify_vernac_ast \
  original.v.jsonl.astdump \
  original.v.classified.jsonl

scripts/classify_vernac_ast \
  candidate.v.jsonl.astdump \
  candidate.v.classified.jsonl
```

The classified format is JSONL schema version 1.  Each record contains:

- the complete raw `astdump` node in `ast`;
- `phase` and `vernac_kind`;
- the official classifier `category` and subtype fields;
- command controls and attributes;
- structured `VernacRequire`, `VernacExtend`, and proof-ending metadata.

Older classification summaries that omit `ast` cannot enforce exterior AST
equality and are rejected.  Regenerate them with the classifier above.

## Validate

```bash
python3 scripts/validate_classified_ast.py \
  original.v.classified.jsonl \
  candidate.v.classified.jsonl \
  --target target_theorem \
  --stage final
```

If exactly one proof changed, `--target` may be omitted and that proof is
selected automatically.  For files containing several unchanged proofs,
specify `--target` to avoid ambiguity.

Use `--stage submission` for a proof-producing subagent that edits only one
authorized local proof region.  In this mode an unchanged baseline terminator
(for example the outer theorem's existing `Admitted.` scaffold) may remain;
if the terminator is changed, it must already be an ordinary opaque `Qed.`.
Use `--stage final` for theorem completion; this retains the strict ordinary
opaque `Qed.` requirement.

The program prints JSON and exits with:

- `0`: AST policy accepted;
- `1`: rejected or malformed classified AST;
- `2`: invalid command-line invocation.

Example rejection:

```json
{
  "accepted": false,
  "rejected": true,
  "target": ["target"],
  "reasons": [
    {
      "code": "PROOF_SIDE_EFFECT",
      "message": "目标 proof body 中出现 VtSideff；可能新增公理、定义、实例、hint 或修改全局状态。",
      "index": 3,
      "line": 3,
      "details": {"vernac_kind": "VernacAssumption"}
    }
  ]
}
```

## Allowlisted imports

No new import is accepted by default.  Add exact raw Require keys with
`--allow-require`:

```bash
python3 scripts/validate_classified_ast.py \
  original.classified.jsonl candidate.classified.jsonl \
  --target target_theorem \
  --allow-require 'mathcomp::all_ssreflect' \
  --allow-require 'prosa.analysis.facts.behavior.service'
```

The key notation follows the source AST:

```text
From mathcomp Require Import all_ssreflect.
    -> mathcomp::all_ssreflect

Require Import prosa.analysis.facts.behavior.service.
    -> prosa.analysis.facts.behavior.service
```

Matching is exact: prefixes and wildcards are not supported.  By default only
`Require Import` (`mode = Import`) is accepted.  `Require`, `Require Export`,
category filters, name filters, controls, and attributes remain rejected unless
the policy is explicitly changed.

## Trusted extension plugins

Rocq's built-in Ltac plugin (`rocq-runtime.plugins.ltac`) is trusted by default.
This is necessary because a candidate may replace an empty or admitted proof,
so the original AST may contain no Ltac extension node at all. Plugin names
already present in the original classified AST are also trusted by default. A
plugin introduced by a newly approved library must be added by its exact
`ext_plugin` name:

```bash
--trusted-plugin rocq-runtime.plugins.ssreflect
```

Use `--no-trust-original-plugins` to require an entirely explicit plugin list.

## Scope

This script is the structural AST policy gate.  Acceptance does **not** mean the
proof is fully validated.  The evaluator must still perform:

1. `coqc`/kernel checking;
2. equality or convertibility of the original and candidate target kernel
   types;
3. `Print Assumptions` plus the configured assumption allowlist;
4. `check_guarded`, `check_positive`, and `check_universes` checks;
5. dependency and, where required, `coqchk` validation.

Location records are ignored during AST comparison.  Consequently, whitespace
and source-position changes are not rejected.  If byte-for-byte preservation
of comments and formatting outside the proof is required, compare the original
source slices in addition to this AST validator.

## ProsaBuddy integration

`packages/opencode/src/tool/coq-ast-audit.ts` runs this pipeline in isolated
temporary directories and is wired into two workflow boundaries:

- `task`: every proof-producing child submission is audited with
  `--stage submission`; a rejection resumes the same child session with the
  exact reason codes and locations before the transaction is handed back.
- `coqc` and `checkpoint`: a candidate that reaches final theorem completion
  is audited with `--stage final` before it can become a committable snapshot or
  be finalized to the workspace.

The audit uses the proof transaction's immutable `baseSource` as its preferred
baseline.  A session binding's canonical source is only a fallback when no
transaction is active.  The default `auto` mode preserves non-proof uses that
have no bound baseline, but once a baseline/theorem is bound the audit fails
closed on missing tooling or execution errors.

Configuration:

```text
OPENCODE_COQ_AST_AUDIT=auto|required|off
OPENCODE_COQ_AST_AUDIT_TIMEOUT_MS=120000
OPENCODE_COQ_AST_AUDIT_MAX_REPAIRS=2
OPENCODE_COQ_AST_TRUSTED_REQUIRE_ROOTS=mathcomp,prosa
OPENCODE_COQ_AST_TRUSTED_PLUGINS=
OPENCODE_COQ_AST_FCC=/path/to/fcc
OPENCODE_COQ_AST_PYTHON=/path/to/python3
OPENCODE_COQ_AST_CLASSIFIER=/path/to/classify_vernac_ast
OPENCODE_COQ_AST_VALIDATOR=/path/to/validate_classified_ast.py
```

`off` is an explicit compatibility escape hatch.  Evaluator deployments that
must reject an unbound or misconfigured audit should set `required`.
