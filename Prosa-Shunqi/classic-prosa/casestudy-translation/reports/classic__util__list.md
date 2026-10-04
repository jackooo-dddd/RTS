# Report: `classic/util/list.v` (rank 9)

| Item | Value |
|---|---|
| Source | ProsaBuddy `f692cb7`, `prosaworkspace/classic/util/list.v` |
| sha256 | `860b96e954873f46f90dfd374f57c60e2a63b5f472e20896fa01b9676525ab85` |
| Lean module | `Prosa/Classic/Util/List.lean` (namespace `Prosa.Classic.Util.List`) |
| Tier / layer | S / 2 |
| Status | **ACCEPTED** (classic validation family; see the manifest) |
| Validation | accepted |

## Declarations (44 source → Lean, same names)

- `Lemma` `idx_lt_rcons`
- `Lemma` `filter_idx_lt_take`
- `Lemma` `filter_idx_le_takeS`
- `Lemma` `mapP2`
- `Lemma` `zipP`
- `Lemma` `mem_zip_exists`
- `Lemma` `mem_zip`
- `Lemma` `mem_zip_nseq_r`
- `Lemma` `mem_zip_nseq_l`
- `Lemma` `unzip1_pair`
- `Lemma` `unzip2_pair`
- `Lemma` `eq_unzip1`
- `Lemma` `eq_unzip2`
- `Fixpoint` `nth_or_none`
- `Lemma` `nth_in_or_default`
- `Lemma` `nth_neq_default`
- `Lemma` `nth_or_none_mem`
- `Lemma` `nth_or_none_mem_exists`
- `Lemma` `nth_or_none_size_none`
- `Lemma` `nth_or_none_size_some`
- `Lemma` `nth_or_none_uniq`
- `Lemma` `nth_or_none_nth`
- `Lemma` `pmap_inj_in_uniq`
- `Lemma` `pmap_inj_uniq`
- `Program Definition` `set_nth_if_exists`
- `Fixpoint` `replace_first`
- `Definition` `replace_first_const`
- `Definition` `set_pair_1nd`
- `Definition` `set_pair_2nd`
- `Lemma` `replace_first_size`
- `Lemma` `replace_first_cases`
- `Lemma` `replace_first_no_change`
- `Lemma` `replace_first_idempotent`
- `Lemma` `replace_first_new`
- `Lemma` `replace_first_previous`
- `Lemma` `replace_first_failed`
- `Definition` `pairs_to_function`
- `Lemma` `pairs_to_function_neq_default`
- `Lemma` `pairs_to_function_mem`
- `Definition` `total_over_list`
- `Definition` `antisymmetric_over_list`
- `Lemma` `in_cat`
- `Lemma` `seq_max_cons`
- `Lemma` `subseq_leq_size`

Missing in Lean: none.
Lean-only helpers (`LEAN_HELPER`, not counted as translated declarations): `getD_lt`, `getD_ge`, `filter_idxOf_lt_eq_take`.

## Representation notes

Lemmas about lists.  The source re-exports `prosa.util.list` (imported above).

Representation notes (following the accepted v0.6 conventions):
* `seq T` is `List T`; `size` is `length`; `uniq` is `Nodup`; `index x l` is
  `l.idxOf x`; `nth x0 l i` is `l.getD i x0`; `rcons s x` is `s ++ [x]`;
  `take`, `filter`, `map`, `zip` are the Lean list functions; `nseq` is
  `List.replicate`; `pmap` is `List.filterMap`; `unzip1`/`unzip2` are
  `List.map Prod.fst`/`List.map Prod.snd`.
* `Context {T : eqType}` is a carrier with `[DecidableEq T]`.
* `is_true (x \in l)` is `x ∈ l` and `x \notin l` is `x ∉ l`; a Boolean equation
  `(x \in a) = (x \in b)` is `decide (x ∈ a) = decide (x ∈ b)`; `~~ b` in
  proposition position is `(!b) = true`.
* `reflect P b` is the informative `BoolReflect P b` (as in the accepted v0.6
  files), defined below as a Lean helper.
* The section-local `Let max := foldl maxn 0` is unfolded in `seq_max_cons`,
  exactly as Rocq abstracts it when the section is closed.
* `set_nth_if_exists` uses `List.set`, which agrees with MathComp's
  `set_nth x0 l n y` whenever `n < size l` (the only case the source uses);
  the default element of the `Program` obligation is therefore irrelevant.
* `set_pair_1nd` is translated faithfully: like the source, it replaces the
  second component.

## History

- 2026-10-01: translated; build and axiom check passed.
- 2026-10-02: translated; build and axiom check passed.
- 2026-10-02: accepted.
