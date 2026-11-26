---
title: Verifereum
lang: en
description: Verifereum is an executable formal semantics of the Ethereum Virtual Machine in the HOL4 theorem prover, validated against the Ethereum execution spec tests, with machine-checked theorems and a program logic for EVM bytecode.
header-includes:
    <link rel="icon" type="image/svg" href="./verifereum-logo-small.svg">
---

# !["Verifereum logo"](verifereum-logo-big.svg "Verifereum")

## Formal semantics of the Ethereum Virtual Machine in HOL4

Verifereum is an executable formal semantics of the [Ethereum](https://ethereum.org) Execution Layer's EVM, mechanised in the [HOL4 theorem prover](https://hol-theorem-prover.org). The semantics runs inside the logic, which is how it is checked against Ethereum's conformance tests, and it is the foundation for machine-checked proofs about EVM bytecode: theorems about the semantics itself, a program logic for contracts, and compiler verification targeting the EVM.

## Status

[Verifereum v1.2.0](https://github.com/verifereum/verifereum/releases/tag/v1.2.0) targets Osaka and is tested against all 17,441 Osaka blockchain cases in the [Ethereum Execution Spec Tests (EEST) v21.0.2](https://github.com/ethereum/execution-specs/releases/tag/tests%40v21.0.2).

The checked runner evaluates the semantics inside HOL4: a Passed result is backed by a kernel-checked theorem. The latest full run passed 17,386 cases (99.7%) in 5h22m on 16 cores; 55 cases timed out, with no other failures ([checked results](table.html)). The unchecked runner compiles the same definitions to native code and runs them without producing proofs. It passed all 17,441 cases (100%) in 38 minutes on CI, including every case that timed out in the checked run ([unchecked results](table-unchecked.html)).

## What's in the repository

The [repository](https://github.com/verifereum/verifereum) is GPLv3. It contains:

- The semantics, in `spec/`: EVM state (`vfmStateScript.sml`), operations (`vfmOperationScript.sml`), and execution (`vfmExecutionScript.sml`) as a definitional interpreter, with block and transaction processing.
- Theorems in `spec/prop/` cover frame and static-call preservation, gas accounting, and correspondence between canonical system-contract bytecode and high-level models under [documented bounds](https://github.com/verifereum/verifereum/blob/main/README.md).
- A program logic, in `prog/vfmProgScript.sml`: a separation-logic model of the EVM, with `EVM_SPEC_SEMANTICS` relating specifications to execution traces.
- Utilities, in `util/`: RLP, Merkle Patricia tries, the contract ABI, and the precompiles' cryptography (secp256k1, secp256r1, BN254, BLS12-381, Blake2f).
- The test driver, in `tests/`, which fetches the EEST fixtures, runs them through the semantics, and writes the results table.

## News

- **July 2026:** The [Ethereum Security QF round](https://forum.giveth.io/t/ethereum-security-qf-round-results-april-23-may-14-2026/2201) brought in $403 in donations and 1.085 ETH in matching funds, primarily for the Glamsterdam update, with some funding for [CakeML translation research](https://github.com/verifereum/verifereum/issues/14). The round also supported [Vyper-HOL](https://github.com/verifereum/vyper-hol). Thanks to all donors, especially [The DAO Fund](https://x.com/TheDAOfund) and [Wintermute](https://x.com/wintermute_t).

## Get involved

- Chat in the [Verifereum channel](https://hol.zulipchat.com/#narrow/channel/verifereum) on the HOL Zulip.
- Pick up an [open issue](https://github.com/verifereum/verifereum/issues), or ask there.
- Read the [contributor guide](/contribute) for how to build the project and where help is needed.
- Donate on [Giveth](https://giveth.io/project/verifereum).

## Related projects

- [Vyper-HOL](https://github.com/verifereum/vyper-hol): a semantics for the [Vyper](https://vyperlang.org) language and verification of its compiler, built on Verifereum.
- [Solidity-HOL](https://github.com/verifereum/solidity-hol): the beginnings of a Solidity semantics in HOL4.
- [HOL4](https://hol-theorem-prover.org): the theorem prover everything here is written in.
