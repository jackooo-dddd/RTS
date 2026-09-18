# Compatibility patches used by the scheduled_in experiment

These patches preserve the exact temporary changes used by the successful
2026-09-18 HKT import and certificate run. They do not patch the RTS Lean
translation.

## rocq-lean-import

Apply `rocq-lean-import-rocq93.patch` to upstream `rocq-lean-import` commit
`546979bfd55b94288abfb72583a534b0136d282d`:

```sh
git checkout 546979bfd55b94288abfb72583a534b0136d282d
git apply /path/to/Validation/patches/rocq-lean-import-rocq93.patch
```

The patch contains the current upstream `fix-UInt32` change plus the Rocq 9.3
API compatibility, Lean 4.33 string representation, and kernel-checked
`Char.ofNatAux` predeclaration used by this experiment. Applying it to the
stated baseline reproduces these file hashes:

```text
0bcd27a0c45bb454ab6a21c518db2f23bbca588bc7a327ae16561b359ad19345  src/Lean.v
ba2b6c3d85c135afad611ea4cc61b37b8541f0eb0502c728eac59ebed7e523b6  src/lean.ml
```

## Prosa v0.6 source compatibility

Apply `prosa-v0.6-rocq93-compat.patch` to the exact Prosa v0.6 archive with
SHA-512
`128dd213e687653a6ad5a55f33e76d39f4301f4fb22ff2c58379bb9d727ada00da776beee213e89b6be117f4db7c7bd73e467e28f57dfbee017891a4121e6228`:

```sh
git apply /path/to/Validation/patches/prosa-v0.6-rocq93-compat.patch
```

The patch contains only syntax/tactic compatibility and a narrowed import in
`behavior/job.v`; it does not change the declarations in `behavior/schedule.v`
or the definition of `scheduled_in`. The successful target closure does not
depend on the `util/list.v` edit, but it is retained so the patch exactly
reproduces the source cache used during the recorded run.
