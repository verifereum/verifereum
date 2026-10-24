# prog: a program logic for EVM bytecode

`vfmProgScript.sml` sets up a separation-logic program logic over the
executable semantics, using HOL's `SPEC` triples (`progTheory`).
`evmDecompLib` builds on it to summarize a contract's runtime code one
basic block at a time.

## Overview

The EVM state is split into resources, each with an assertion: the
stack (`evm_Stack`), the program counter (`evm_PC`), gas used
(`evm_GasUsed`), memory (`evm_Memory`), the rollback state with storage
and accounts (`evm_Rollback`), logs (`evm_Logs`), the message parameters
(`evm_MsgParams`), and so on. A triple

```
SPEC EVM_MODEL pre code post
```

says that from any state satisfying `pre`, with the instructions `code`
at their pcs, execution reaches a state satisfying `post`, and that the
resources `pre` doesn't mention are left alone. A `cond c` conjunct in
`pre` is a side condition that must hold.

`vfmProgTheory` proves one such rule per instruction, named
`SPEC_<opcode>`: `SPEC_Add`, `SPEC_SLoad`, `SPEC_Push` (for any `n` and
bytes), `SPEC_JumpI_take` and `SPEC_JumpI_skip`, `SPEC_Return_outermost`
(for both RETURN and REVERT), `SPEC_Call` (whose post is the callee's
frame), and so on. Larger triples are composed from these with
`SPEC_COMPOSE` and `SPEC_FRAME`.

## Block summaries

Composing rules by hand for a whole contract is long and fragile: a
contract has hundreds of instructions, and each composition step needs
the stack spelt out and the side conditions tidied. `evmDecompLib` does
it mechanically. Given the runtime code, `summarize_code` returns one
theorem for each basic block and each way out of it. Every theorem is
proved from the `vfmProgTheory` rules by `SPEC_REFL`, `SPEC_FRAME`,
`SPEC_COMPOSE` and `SPEC_MOVE_COND`, so the library adds nothing to the
trusted base: a bug in it produces a failed summary, never a false
theorem.

A block starts at pc 0, at a JUMPDEST, after a JUMPI, after a CALL-class
instruction, or at an extra pc given as a hint. It runs to its
terminator (JUMP, JUMPI, STOP, RETURN, REVERT, INVALID, SELFDESTRUCT, or
a CALL-class instruction) or up to the next block start. A terminator
with several rules gives one summary per rule: a JUMPI block gives a
`take` summary and a `skip` summary.

A summary for a block at pc `n` that reads `d` stack slots and leaves `k`
has this shape:

```
SPEC EVM_MODEL
  (evm_Stack (s0::...::s(d-1)::rest) * evm_PC n * <resources> *
   cond C * cond G)
  {(n,i0); (n+1,i1); ...}
  (evm_Stack (e0::...::e(k-1)::rest) * evm_PC x * <resources'>)
```

- The stack is eliminated. `rest` is never inspected; the `e`s and every
  resource in the post are terms over the `s`s and the entry resources
  (`p.caller`, the memory `m`, the rollback state `rb`, ...). No
  intermediate stack survives, which is what makes the summaries
  readable and composable.
- `C` is what the block needs to run: the stack-depth bound, the absence
  of a pending exception, the JUMPI condition, that `p.code` and
  `p.parsed` are the contract's code (when a jump target or a code read
  depends on it), static-context and access-list facts.
- `G` is the gas layer: the conjuncts mentioning `p.gasLimit`. The chain
  of per-instruction bounds `g + c ≤ p.gasLimit` is collapsed to the
  strongest. Keeping it apart from `C` lets a reader skip the gas
  arithmetic, but it can't be dropped from the precondition, since the
  block does need the gas. `drop_gas` instead hides the gas used in the
  post.

Next to each theorem, `summarize_code` returns a `block_summary` record
read off the theorem: the entry pc, the exit (a JUMP and its target, a
JUMPI taken or not, a fall-through, a halt, or a call), `d` and `k`, the
entry and exit stacks, `C`, `G`, and the ordered effects, one per
instruction that changed a resource other than the stack, pc, gas used
and jump-dest. `block_summary_to_string` prints it. A block that can't be
summarized gives a `Failed` outcome with the pc, instruction and reason;
a variant whose conditions simplify to false (a JUMPI whose condition is
decided) gives `Infeasible`.

`compose_blocks` composes summaries along a path: each summary's
precondition is instantiated from the previous post, so constant jump
targets are resolved and the jump-dest checks discharged.

## Rules

The rules come from a table keyed by the opcode constructor's name. By
default a name maps to `vfmProgTheory`'s `SPEC_<name>`; JUMPI, the
halting instructions and the CALL-class instructions have explicit
entries. A rule is matched against the instruction by its code (or its
`evm_Parsed` assertion), so parameterised rules need no special
handling. `add_rules` and `set_rules` add or replace the rules for an
opcode, which is how new rules (another SELFDESTRUCT or CREATE rule, a
rule for a nested call) plug in without changing the library.

## Hints

The library finds block starts from the code alone. A compiler knows
more: the Solidity compiler's `--asm-json` output and Vyper's assembly
output label every jump target and every function entry, including
targets that are only reached through computed jumps. Those pcs go in
`config.hints`, and each becomes a block start. Hints can only add
starts, and every summary is still proved, so a wrong hint costs a
smaller block, never soundness.

## Example

`examples/wrappedEtherScript.sml` summarizes the WETH runtime code
without hints and stores each summary as a theorem,
`weth_block_<pc>[_<variant>]` (for example `weth_block_0_take`):

```sml
val weth_config : evmDecompLib.config =
  {code_eq = contract_code_eq, parsed_eq = parsed_contract_code_eq,
   hints = [], simps = [mask_and_w2w]}
val weth_outcomes = evmDecompLib.summarize_code weth_config
```

`simps` are extra rewrites for the contract's terms. They run after
every instruction, so they must be cheap: WETH's memory-buffer lemmas
(reading back what was written, memory costs of expanded memory) make
the larger blocks take minutes instead of a second. The script uses
them only to compose the fallback path (blocks 0, 175 and 1088), where
they turn the memory and gas into the same form as the hand-composed
`SPEC_fallback`, and then proves `SPEC_fallback` again from that path
(`SPEC_fallback_blocks`).
