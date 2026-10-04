# Prosa-theorem benchmark (ProsaBuddy train/test set)

130 theorems of Prosa itself, the evaluation set of [ProsaBuddy](https://github.com/ProsaBuddy/ProsaBuddy): 65
training and 65 test theorems, each graded at a difficulty level from 1 to 7, drawn from Prosa v0.6 and classic
Prosa. In ProsaBuddy a task removes one theorem's proof from its Rocq file and asks the agent to prove it again.
Here the same theorems are posed in the Lean library of this package: the theorem's proof is replaced by
`sorry` in its Lean file, and the model must complete it in place.

The task list is ProsaBuddy's table `prosabuddy_train_and_test_data.pdf` (copied from the ProsaBuddy repository,
commit `f692cb7`, MIT license), transcribed in `prosabuddy_dataset.csv`. Every Lean statement was checked against
the original Rocq statement (see the package README), so a Lean task asks for the same theorem as the Rocq one.

## Tasks

`tasks.json` lists the 130 tasks in the table's order (`train-01` … `train-65`, `test-01` … `test-65`):

| Field | Meaning |
|---|---|
| `split`, `level` | ProsaBuddy's split (`train`/`test`) and difficulty level (1–7) |
| `rocq_file`, `rocq_theorem` | the entry of ProsaBuddy's table |
| `lean_file`, `lean_module`, `lean_declaration` | where the theorem lives in this package |
| `statement` | the Lean statement (read-only) |
| `available` | whether the theorem has a Lean counterpart (all 130 do) |
| `holed_sha256` | sha256 of the task file after `prepare.py` |
| `proof_lines` | length of the existing Lean proof (for reference only) |
| `note` | remarks on the entry |

All 130 tasks are available. `train-15` (`job_arrival_is_bounded`, `bounded_bi/jlfp.v`) is a Rocq `Local Lemma`
of a section. In Lean it is the theorem `Prosa.Analysis.Abstract.RestrictedSupply.BoundedBi.Jlfp.job_arrival_is_bounded`,
whose binders are those of the lemma's elaborated Rocq type (the section variables and hypotheses it uses), and
whose statement was certified against that type like every other theorem. ProsaBuddy's table lists
`max_distance_in_nontrivial_seq_is_positive` twice (`train-33` and `train-40`); both rows are kept.

## How a task works

1. Make a working copy of this package for the model, and build it once:
   ```sh
   cp -R lean-prosa-v06 work && cd work && lake exe cache get && lake build && cd ..
   ```
   The model must never see the original package: its Lean files contain the original proofs.
2. Prepare the task (run from the original package):
   ```sh
   python3 lean-prosa-v06/benchmark/prosa-theorems/prepare.py test-07 --workdir work
   ```
   This restores every library file of `work` to the original (undoing earlier tasks), replaces the task's proof
   by `sorry`, and deletes the compiled files of that module (they contain the original proof).
3. Give the model the task: its file, theorem and statement (`PROMPT.md` is a template). It edits only the proof
   of that theorem, and can run `lake build <module>` in `work`.
4. Check (run from the original package):
   ```sh
   python3 lean-prosa-v06/benchmark/prosa-theorems/check.py test-07 --workdir work [--json result.json]
   ```

Running many tasks in one working copy: after a task in a low-level module (for example `Prosa.Util.Nondecreasing`),
Lake recompiles the modules that depend on it the next time they are needed. Running the tasks with the most
downstream modules first keeps this cheap, and on a 16 GB machine `LEAN_NUM_THREADS=2` to `4` avoids swapping.

The checker accepts a solution only if:
- no other library file changed and none was added;
- the task file differs from the prepared file only inside the theorem's proof (the proof must stay indented
  below the theorem);
- the proof has no forbidden token (`sorry`, `admit`, `axiom`, `unsafe`, `implemented_by`, `@[extern`,
  `skipKernelTC`, `addDeclWithoutChecking`, `set_option debug.`, `run_cmd`, `run_elab`, `run_meta`, `#eval`,
  `initialize`, `elab`, `elab_rules`);
- `lake build <module>` succeeds;
- `#print axioms <theorem>` lists only `propext`, `Classical.choice` and `Quot.sound`.

## What the model may use

As in ProsaBuddy, the model may use everything its file can see: the imported modules (all of Mathlib and the
Prosa modules the file imports) and the declarations above the theorem in the same file. Declarations below the
theorem, and modules that import the file, are not visible to Lean at that point. Helper lemmas must be stated
inside the proof (`have`).

Two differences from the Rocq setting are worth recording when comparing results:
- Rocq section variables and hypotheses are explicit binders of the Lean statement.
- Some Lean files contain extra helper lemmas that are not in the Rocq file (marked `LEAN_HELPER` in their
  docstrings). They were added for the translation. Lemmas above the theorem are visible to the model, as in
  Rocq.

## Reporting

Report pass@k per split (`train`, `test`) and per level.

## Reference proofs

The existing proof in the original package is a reference solution for every task. To check the checker itself:
prepare a task, copy the original file back into `work`, and run `check.py`. It must print `PASS`.
