# prog: a program logic for EVM bytecode

`vfmProgScript.sml` sets up a separation-logic program logic over the
executable semantics, using HOL's `SPEC` triples (`progTheory`).

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

`vfmProgCallTheory` has the caller-side CALL rules: `SPEC_Call_any`
takes a CALL to arbitrary code straight to the caller's next
instruction, and `SPEC_Call_stipend` adds that a callee given at most
the 2300-gas stipend changes no account beyond the call's own value
transfer.
