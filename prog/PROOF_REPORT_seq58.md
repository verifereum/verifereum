# seq58 vfmProg proof repair: delivery audit

## Scope and source result

The proof-only diff against the owner-corrected frozen base `dab86201` adds three local arithmetic lemmas and repairs four existing proofs. No existing theorem statement or definition was changed. `spec/`, `tests/`, the required historical witnesses, and the existing repayment helpers were untouched. The source has no active `cheat`; its remaining textual occurrence is in a pre-existing commented example. The diff adds no definitions, axioms, timeout changes, or search tactics under TRY/ORELSE.

## Repaired proofs

| Theorem | Tactic change |
| --- | --- |
| `SPEC_Return_inner` | Normalize the Revert child's capped spill refund using `restored_unused_gas` and `asm_simp_tac pure_ss` before symbolic execution; separate `restore_state_gas` execution from context popping. Normalize repayment/absorption and the `merged` abbreviation in the Return branches. Remove an obsolete arithmetic conjunct step. |
| `SPEC_Invalid_outermost` | Stage simplification of restoration/forfeiture, then remaining-gas consumption before `end_tac`. |
| `SPEC_Invalid_inner` | Normalize restoration/forfeiture before splitting the destination; then normalize the remaining monadic operations, context pop, absorption, and `merged`/`caller` abbreviations. |
| `SPEC_SelfDestruct_inner` | Add a final repayment/absorption normalization stage, including `merged` and the remaining monadic operations, after context incorporation. |

`SPEC_Invalid` and `SPEC_SelfDestruct_outermost` passed unchanged. Earlier repaired families are preserved as present in the frozen base.

## Added helper statements

All three are local theorems, not definitions:

```sml
Theorem restored_unused_gas[local]:
  x <= limit ==> limit - (x - sp) = (limit - x) + MIN sp x
```

Proof: split on `sp <= x`, simplify `MIN_DEF`, and use `decide_tac`.

```sml
Theorem restored_unused_gas_bound[local]:
  x <= limit /\ (limit - x) + MIN sp x <= callerGas ==>
  limit - (x - sp) <= callerGas
```

Proof: rewrite with `restored_unused_gas` using `asm_simp_tac pure_ss`.

```sml
Theorem restored_unused_gas_sub[local]:
  x <= limit ==>
  callerGas - (limit - (x - sp)) = callerGas - (limit - x) - MIN sp x
```

Proof: the same pure rewrite followed by `decide_tac`.

## Commits

- `e188cc70`: scalar restoration helpers.
- `3ea22897`: corrected Return proof.
- `6dd14bb6`: Invalid frame proofs.
- `6223f2c6`: SelfDestruct inner proof.

Each has the required `Bot: deepseek (DeepSeek V4.1 Flash)` trailer.

## Build and certification limitation

The supported tool invocation is `holbuild(targets=["vfmProgTheory"], timeout=900)`. The actual build after the final proof edit reported:

```
resuming vfmProgTheory
  from: failed-prefix checkpoint in SPEC_SelfDestruct_inner
  restoring proof-ir prefix with 49 successful leaf steps
vfmProgTheory built
holbuild finished in 17.331s
```

The final audit invocation succeeded in 0.095 seconds (up-to-date target). This is not a fresh uncached replay, and the interface does not expose CLI parallelism or force/no-cache/skip-checkpoint flags.

The accessible public log `.holbuild/logs/current/verifereum/vfmProgTheory/build.log` currently says:

```
Saved CHEAT _________ "SPEC_SelfDestruct_inner"
Exporting theory "vfmProg" ... done.
Theory "vfmProg" took 3.4s to build
```

The generated `.holbuild/obj/prog/vfmProgTheory.dat` also contains `cheat` oracle metadata in addition to `DISK_THM`. Oracle tags can propagate from imported theorems, and this worktree intentionally includes cheated `spec/prop` scaffolding. However, this audit has not established the precise provenance of every tag or reconciled the public log with the current source/checkpoint success. Therefore this report does **not** certify an oracle-free theory or satisfaction of the literal no-Saved-CHEAT log criterion. This is an unresolved build/trust certification limitation, not a counterexample to the frozen rules.

Completion needs an externally supported fresh source replay and trustworthy updated log, followed by classification of any surviving scaffold-derived oracle tags. Do not repair the forbidden scaffold, alter frozen statements, or suppress artifact metadata to achieve that. No EEST/tests were run.
