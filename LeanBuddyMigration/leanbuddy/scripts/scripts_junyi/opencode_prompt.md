# Coq Theorem-Proving Benchmark

You are running a Coq theorem-proving benchmark with the original opencode agent.

## Objective

Complete the proof in the designated working `.v` file.

A run is successful only if the target proof ends with `Qed.` and the file compiles successfully with `coqc`.
Important: Exit only when this is achieved!!!

## Hard Read Scope

You may read only the following workspace content:

- the single target `.v` file that is being tested
- the workspace-local `proof.tex` file, if it exists
- the `prosa/` directory inside the current workspace

You must not read anything else.

This prohibition includes:

- any other file or directory inside the workspace
- any file or directory outside the workspace
- any `.pdf` file
- any `.tex` file other than the workspace-local `proof.tex`
- any `.md`, `.json`, `.jsonc`, `.yaml`, `.yml`, `.log`, `.aux`, `.glob`, or similar artifact outside `prosa/`
- shell history, editor metadata, cache files, previous run outputs, result folders, trace folders, git history, home-directory files, or system files

Do not expand the read scope even if the proof is difficult.

## Write Scope

You may modify only the target `.v` file.

You must not:

- modify `prosa/`
- modify any other workspace file
- create helper files, scripts, notes, or temporary proof files
- change theorem statements, imports, module structure, or any text outside existing proof blocks

## Forbidden Shortcuts

Do not introduce, leave behind, or rely on any fake assumption, placeholder proof, or proof-skipping device.

Unless a narrower runtime instruction explicitly authorizes a temporary admit-based skeleton for the current attempt, the following are forbidden:

The following are explicitly forbidden:

- `Hypothesis`
- `Axiom`
- `Parameter`
- `Variable`
- `admit`
- `Admitted`
- `Abort`

Do not weaken the theorem statement, do not replace the benchmark with a different task, and do not "solve" the problem by changing specifications.

## Terminal Policy

The only terminal command you may run is the compilation command for the working file:

- `coqc <working-file>.v`

Do not use the terminal for search, discovery, file inspection, environment inspection, logging, or any other command.

## Proof Policy

- Keep changes minimal and local.
- Preserve the existing proof structure whenever possible.
- Reuse only facts available from the target `.v` file and from `prosa/`.
- After each meaningful edit, run `coqc` on the working file.
- If compilation fails, fix the proof and compile again.

If the theorem cannot be completed under the allowed context, report the exact blocker instead of adding assumptions or placeholders.

## Workspace Boundary

You must not read, browse, inspect, or edit anything outside the current workspace directory.

This means:

- No reading files in parent directories
- No accessing home directory files
- No inspecting system files or environment variables
- No browsing git history outside the workspace
- No accessing any path that is not inside the current working directory

## Success Criteria

The task is complete only if all of the following are true:

- the target theorem is fully closed with `Qed.`
- `coqc` succeeds on the working `.v` file
- no forbidden assumption or placeholder proof was introduced
- nothing outside the allowed read scope was accessed
- no file other than the target `.v` file was modified

Do not stop before these conditions are satisfied.
