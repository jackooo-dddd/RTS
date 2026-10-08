# Case-study proof benchmark

23 theorems from real-time scheduling papers, stated in Lean 4 over classic Prosa (`Prosa.Classic.*`). Each
task asks for a complete, axiom-free Lean proof of one statement. The checker accepts a proof only if it
proves exactly the frozen statement.

The statements come from the Rocq case studies `RTS_Papers/<task>/…` written against classic Prosa. Each was
translated to Lean with the same definitions, binders and hypotheses (see the docstring of each task's
`Statement.lean`). All 23 are provable: reference proofs exist and are distributed separately (see
"Reference solutions" below).

## Papers and tasks

- Bertogna, Cirinei, Lipari — Improved Schedulability Analysis of EDF on Multiprocessor Platforms (ECRTS 2005): `2005-ECRTS-Lemma3`, `2005-ECRTS-Lemma4`, `2005-ECRTS-Theorem6`
- Bertogna, Cirinei — Response-Time Analysis for Globally Scheduled Symmetric Multiprocessor Platforms (RTSS 2007): `2007-RTSS-Theorem1`, `2007-RTSS-Theorem2`, `2007-RTSS-Theorem3`, `2007-RTSS-Theorem4`
- Guan, Stigge, Yi, Yu — New Response Time Bounds for Fixed Priority Multiprocessor Scheduling (RTSS 2009): `2009-RTSS-Extend1_10`, `2009-RTSS-Lemma1`, `2009-RTSS-Lemma1_2`, `2009-RTSS-Lemma2-1`, `2009-RTSS-Lemma2-2`, `2009-RTSS-Lemma3`, `2009-RTSS-Lemma4`, `2009-RTSS-Lemma5`, `2009-RTSS-Method1`, `2009-RTSS-Theorem1`, `2009-RTSS-Theorem2`
- Improving the Response Time Analysis of Global Fixed-Priority Multiprocessor Scheduling (RTCSA 2014): `2014-RTCSA-Lemma4`, `2014-RTCSA-Lemma5`, `2014-RTCSA-Theorem3`
- Baruah, Bertogna, Buttazzo — Multiprocessor Scheduling for Real-Time Systems (book, 2015), Lemma 18.1: `2015-BOOK-Lemma18.1`
- Linux push/pull scheduler with arbitrary processor affinities (2015), Lemma 8 (APA): `2015-RTAS-Lemma8`

## Layout

Each task has its own folder, `CaseStudies/<G>/<F>/` (for example `CaseStudies/RTSS2007/Theorem1/` for task
`2007-RTSS-Theorem1`; `benchmark/tasks.json` gives the folder of every task):

| Path | Role | Model may edit? |
|---|---|---|
| `CaseStudies/<G>/<F>/Statement.lean` | Definitions of the case study and `<thm>_statement : Prop` | no |
| `CaseStudies/<G>/<F>/proof.tex` | Hint: the paper's statement and proof sketch (LaTeX), where available | no |
| `CaseStudies/<G>/<F>/Solution.lean` | `theorem solution : <thm>_statement := by sorry` | **yes** |
| `CaseStudies/**` (new `.lean` files) | Helper modules, if wanted | **yes** |
| `Prosa/**` | The library (Prosa v0.6 and classic Prosa) | no |
| `benchmark/tasks.json` | Task list (ids, folders, modules, statement and solution names, hint file) | no |
| `benchmark/check.py` | The checker | no |

21 of the 23 tasks have a hint; `2009-RTSS-Extend1_10` and `2009-RTSS-Method1` have none (their `hint_file` in
`tasks.json` is `null`).

## Rules for a solution

- Replace the `sorry` in `CaseStudies/<G>/<F>/Solution.lean` with a proof. Keep the name `solution` and its
  type.
- Allowed: `import` of any module of this package (`Prosa.*`, `Mathlib.*`, statement modules, your own helper
  modules), helper definitions and lemmas, any tactics, and new `.lean` files under `CaseStudies/`.
- Not allowed: editing `Statement.lean`, `proof.tex` or anything outside `CaseStudies/`; `sorry`, `admit`, new
  `axiom`s; kernel-bypassing or meta-programming escapes. The checker rejects the tokens `unsafe`,
  `implemented_by`, `@[extern`, `skipKernelTC`, `addDeclWithoutChecking`, `set_option debug.`, `run_cmd`,
  `run_elab`, `run_meta`, `#eval`, `initialize`, `elab`, `elab_rules` in the solution and in every helper
  module it imports.
- The proof may use only Lean's standard axioms `propext`, `Classical.choice`, `Quot.sound`, so
  `native_decide` is not allowed either.

## Checking

```sh
python3 benchmark/check.py                         # all tasks
python3 benchmark/check.py 2009-RTSS-Lemma3        # one task
python3 benchmark/check.py --json results.json     # also write machine-readable results
```

For each task the checker:

1. verifies that no read-only file changed (sha256 list in `frozen_sha256.json`: the library, every
   `Statement.lean` and `proof.tex`, the configuration; added files under `Prosa/` also count),
2. scans the solution and the helper modules it imports for forbidden tokens,
3. runs `lake build <solution module>`,
4. compiles a fresh file containing `theorem benchmark_check : <statement> := <solution>` and
   `#print axioms benchmark_check`, and accepts only the three standard axioms.

Step 4 makes the check independent of how the solution file is written: the statement is a closed `Prop`
constant elaborated in the read-only module, so nothing a solver writes can change its meaning. The output
is one `PASS`/`FAIL` line per task with the reason, plus a summary; the exit code is 0 only if every
selected task passed.

On the unmodified package every task fails with "forbidden token(s) …: sorry".

## Running an evaluation

1. Give the model this folder (without the reference solutions) and a built `.lake` (run `lake exe cache get`
   and `lake build` first, so the model's own builds are fast).
2. Per task, give the model the task id and its folder (statement, hint, solution file). `PROMPT.md` is a
   prompt template. Let it read the library and run `lake build <solution module>` or `lake env lean <file>`.
3. Run `python3 benchmark/check.py <task-id>` on the result. Use a fresh copy of the folder for each task
   (or restore the `Solution.lean` files, remove added files, and run the frozen-file check) so that tasks
   don't share work.
4. Report pass@k per task and overall.

## Notes on individual statements

Some statements keep features of the Rocq originals that look unusual. They are part of the task as stated:

- `2005-ECRTS-Theorem6`: Stated as an equivalence (schedulable ⟺ condition), whereas the paper's Theorem 6 is a sufficient test; translated as written.
- `2007-RTSS-Theorem3`: Hypothesis `constrained_deadline_model task_deadline task_period ts` has period/deadline swapped in the source; translated as written.
- `2009-RTSS-Extend1_10`: Source does not compile as written (`[seq fst p <- hp_bounds]`, line 232); translated with the map `[seq fst p | p <- hp_bounds]` as in 2009-RTSS-Method1.
- `2009-RTSS-Lemma2-2`: `Non_CI` compares the relative `job_deadline j0` with the instant `t0 sched j`, as written.
- `2009-RTSS-Theorem2`: In the source, `f_chi` passes `h` and `num_cpus` to `total_interference_bound_gn_arbitrary` in swapped positions; translated as written.
- `2014-RTCSA-Lemma4`: The conclusion binds its own `tsk_other`, `R_other` (the chain hypotheses are about the section variables of the same names).
- `2014-RTCSA-Theorem3`: Hypothesis `exist_j_released_at_criticalinstant` parses as `∃ j, (arrives ∧ task) → arrival = critical_instant`, as written.
- `2015-RTAS-Lemma8`: Local `W` uses the interfering task's deadline instead of its response-time bound (differs from the classic APA analysis).

Several case studies take earlier lemmas of their paper as hypotheses (for example `H_Lemma2_1`,
`Lemma1_09`); those hypotheses may be used as given.

## Reference solutions

Reference proofs of all 23 tasks are in the separate folder `lean-prosa-v06-reference-solutions/`. Do not give
it to a model under evaluation. To verify them, copy its `CaseStudies/` folder over this one (it replaces each
`Solution.lean` and adds the shared helper modules `CaseStudies/Support/*`) and run the checker:

```sh
cp -R ../lean-prosa-v06-reference-solutions/CaseStudies .
python3 benchmark/check.py          # 23/23 passed
```
