<div align="center">

# ProsaBuddy

### Assisting Mechanized Real-Time Schedulability Analysis with LLM-Based Agents

ProsaBuddy is a research prototype for developing and repairing Rocq/Coq proofs in
[Prosa](https://prosa.mpi-sws.org/), with a focus on mechanized real-time schedulability analysis.

</div>

## Overview

ProsaBuddy combines a terminal-based coding-agent interface with a proof-oriented, multi-agent workflow. It is
designed to help navigate large Prosa developments, construct theorem-level proof plans, solve local proof regions,
diagnose failures, and validate changes with the Rocq/Coq toolchain.

The project is built on [OpenCode](https://github.com/anomalyco/opencode) and extends it with agents, tools, skills,
and execution guards specialized for mechanized proofs. A Prosa proof workspace is included so that proof search and
validation can operate against a concrete real-time systems formalization.

> ProsaBuddy is experimental research software. Generated proofs should be reviewed and accepted only after they
> have been checked by Rocq/Coq in the intended project environment.

## Key Capabilities

- **Hierarchical proof solving:** separates theorem-level planning from local proof-region construction and repair.
- **Prosa-aware exploration:** searches relevant definitions, lemmas, notations, and nearby proof patterns before
  editing a theorem.
- **Structured proof plans:** records proof phases, dependencies, ownership of proof regions, and recovery decisions.
- **Transactional proof editing:** stages localized edits and validates them before accepting a checkpoint.
- **Compiler-backed verification:** integrates `coqc`, `coqtop`, proof goals from LSP, and Petanque-based interaction.
- **Bounded recovery:** classifies failures, delegates focused repair, and revises a plan without unconstrained
  rewriting.
- **Execution safeguards:** limits edits to the intended proof region and guards long-running or unsafe proof-tool
  operations.

## Proof Workflow

ProsaBuddy uses several cooperating agent roles:

| Agent | Responsibility |
| --- | --- |
| `prover` | Builds the theorem-level proof architecture, coordinates phases, and controls checkpoints. |
| `lemma` | Solves a bounded local proof region under the current plan. |
| `fixer` | Repairs a focused proof or compilation error. |
| `diagnoser` | Classifies failures and recommends the next recovery action. |
| `explorer` | Performs read-only searches for definitions, lemmas, and reusable proof patterns. |
| `whole-lemma` | Attempts a direct whole-theorem proof as a bounded fallback. |

These roles are supported by dedicated proof-planning, Coq-session, compiler, checkpoint, and search tools. The
workflow maintains a proof dependency graph and uses compiler-certified checkpoints to decide whether a proposed
change can be retained.

## Repository Layout

```text
.
├── .opencode/                  # Project agents, skills, commands, themes, and configuration
├── packages/opencode/          # ProsaBuddy's terminal application and proof-tool integrations
├── packages/plugin/            # Plugin interfaces
├── packages/sdk/               # JavaScript SDK
├── prosaworkspace/             # Bundled Prosa proof workspace
│   └── rt-proofs-v0.6/         # Prosa real-time systems development
├── scripts/                    # Project utility scripts
└── train_and_test_data.pdf     # Description of the evaluation datasets
```

## Requirements

- [Git](https://git-scm.com/)
- [Bun](https://bun.sh/) 1.3.x (tested on Bun 1.3.10)
- Rocq or Coq available on `$PATH`
- The dependencies required by the bundled Prosa development, including MathComp ssreflect and
  `mczify`/`mathcomp-zify` when recompiling its proofs
- Credentials for a supported LLM provider

The exact Rocq/Coq and library versions should match the target proof development. See
[`prosaworkspace/rt-proofs-v0.6/README.md`](prosaworkspace/rt-proofs-v0.6/README.md) for the bundled Prosa release's
build information.

## Installation

```bash
git clone https://github.com/ProsaBuddy/ProsaBuddy.git
cd ProsaBuddy
bun install
```

## Quick Start

Start ProsaBuddy from the repository root:

```bash
bun run dev
```

Configure a supported model provider in the terminal interface, then open or describe a target theorem under
`prosaworkspace/`. Ask the `prover` agent to inspect the theorem and construct a proof plan before making changes.

A productive request should identify the target file and theorem and state any constraints on the editable proof
region. For example:

```text
Inspect the target theorem in prosaworkspace/<path-to-file>.v, build a proof plan,
and attempt a compiler-checked proof without modifying unrelated lemmas.
```

For reproducible experiments, record the repository revision, model and provider, model parameters, Rocq/Coq
environment, selected theorem, and final compiler output.

## Training and Test Data

The evaluation corpus contains 65 training theorems and 65 test theorems drawn from Prosa and stratified across
seven difficulty levels. It covers theorem files from both modern and classic parts of the development.

The theorem selection and dataset composition are documented in
[`train_and_test_data.pdf`](train_and_test_data.pdf).

## Research and Reproducibility

ProsaBuddy is intended to support research on LLM-assisted formal proof engineering. Results can depend on the model,
provider, prompt configuration, toolchain versions, and repository revision. The repository includes the proof-agent
implementation and dataset description, but it does not by itself guarantee identical outputs from remote or
nondeterministic language models.

When reporting results, pin this repository to a commit and preserve the complete proof-checking environment. Rocq/Coq
acceptance, rather than the agent's textual response, should be treated as the correctness criterion.

## Citation

Citation information will be added after the accompanying paper is published.

## Acknowledgments

ProsaBuddy is built on [OpenCode](https://github.com/anomalyco/opencode), which provides the underlying terminal agent
application and extensible tooling architecture. The bundled formal development comes from
[Prosa](https://prosa.mpi-sws.org/), a formally verified library of definitions and results for real-time systems
analysis. ProsaBuddy is an independent research project and is not maintained by the OpenCode or Prosa teams.

## License

The ProsaBuddy/OpenCode-derived code at the repository root is distributed under the [MIT License](LICENSE). The
bundled Prosa release in `prosaworkspace/rt-proofs-v0.6/` is distributed separately under its
[BSD 2-Clause License](prosaworkspace/rt-proofs-v0.6/LICENSE). Copyright notices and license terms in vendored or
third-party components remain applicable.
