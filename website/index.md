---
title: Verifereum
lang: en
description: Verifereum is an executable formal semantics of the Ethereum Virtual Machine in the HOL4 theorem prover, validated against the Ethereum execution spec tests, with machine-checked theorems and a program logic for EVM bytecode.
header-includes:
    <link rel="icon" type="image/svg" href="./verifereum-logo-small.svg">
---

# !["Verifereum logo"](verifereum-logo-big.svg "Verifereum")

## Formal semantics of the Ethereum Virtual Machine in HOL4

Verifereum is an executable formal semantics of the [Ethereum](https://ethereum.org) Execution Layer's EVM, mechanised in the [HOL4 theorem prover](https://hol-theorem-prover.org). The semantics runs inside the logic, which is how it is checked against Ethereum's conformance tests, and it is the foundation for machine-checked proofs about EVM bytecode: theorems about the semantics itself, a program logic for contracts, and compiler verification targeting the EVM. Audits find bugs; proofs rule out whole classes of them, and Ethereum's small, deterministic programs are a good fit for that.

## Status

The semantics targets the live fork, Osaka. At the last full run it passed 17249 of the 17550 Osaka blockchain tests in the [Ethereum Execution Spec Tests (EEST)](https://steel.ethereum.foundation/docs/execution-specs/) v21.0.1 (98.3%); the [results table](table.html) lists every test and is where the current numbers are. The remaining tests are mostly timeouts in our evaluation (the semantics is not built for speed), plus the tests that use modified system contracts.

## What's in the repository

The [repository](https://github.com/verifereum/verifereum) is GPLv3. It contains:

- The semantics, in `spec/`: EVM state (`vfmStateScript.sml`), operations (`vfmOperationScript.sml`), and execution (`vfmExecutionScript.sml`) as a definitional interpreter, with block and transaction processing.
- Theorems about the semantics, in `spec/prop/`: frame theorems about what execution can touch, such as `run_call_preserves_storage_outside_accessed_slots` in `vfmRunCallScript.sml` (a storage slot a call never accesses is unchanged by it) and `run_static_preserves` in `vfmStaticCallsScript.sml` (a static call changes no account, transient storage, or deletion); the gas accounting theorems of `vfmDecreasesGasScript.sml`; and the `preserves` combinators of `vfmPreservesScript.sml` for proving invariants of the monadic semantics.
- A program logic, in `prog/vfmProgScript.sml`: a separation-logic model of the EVM, with `EVM_SPEC_SEMANTICS` relating specifications to execution traces.
- Examples, in `examples/`: the WETH contract (`wrappedEtherScript.sml`), with `deploy_result_correct` proving that deploying its bytecode produces the expected state.
- Utilities, in `util/`: RLP, Merkle Patricia tries, the contract ABI, and the precompiles' cryptography (secp256k1, secp256r1, BN254, BLS12-381, Blake2f).
- The test driver, in `tests/`, which fetches the EEST fixtures, runs them through the semantics, and writes the results table.

## News

- **July 2026:** Verifereum received $403 in donations and 1.085 ETH in matching funds in the [Ethereum Security QF round](https://forum.giveth.io/t/ethereum-security-qf-round-results-april-23-may-14-2026/2201). The funding will primarily support updating our formal EVM semantics for Glamsterdam, with remaining funds supporting infrastructure work such as [researching a proof-producing translation to CakeML](https://github.com/verifereum/verifereum/issues/14). Support associated with the round has also enabled significant progress in [Vyper-HOL](https://github.com/verifereum/vyper-hol). Thank you to all contributors, especially [The DAO Fund](https://x.com/TheDAOfund) and [Wintermute](https://x.com/wintermute_t) for their major donations.
- **February 2025:** We hosted our first community event, Higher Order Log Cabin, bringing together researchers and developers.

## Talks

- [Towards a verified Vyper → EVM compiler in HOL4](talks/EthProofs2026/), EthProofs project status, June 2026.
- [Verifereum update](talks/EVMTrack2025Q1/), EVM track call, March 2025.
- [Verifereum](talks/HOL4Users2024/), HOL4 Users' Workshop, June 2024.
- [Verifereum](talks/ETHDenver2024/), ETHDenver Lift Off, March 2024.

## Get involved

- Chat in the [Verifereum channel](https://hol.zulipchat.com/#narrow/channel/verifereum) on the HOL Zulip.
- Pick up an [open issue](https://github.com/verifereum/verifereum/issues), or ask there.
- Read the [contributor guide](/contribute) for how to build the project and where help is needed.
- Donate on [Giveth](https://giveth.io/project/verifereum).

## Related projects

- [Vyper-HOL](https://github.com/verifereum/vyper-hol): a semantics for the [Vyper](https://vyperlang.org) language and verification of its compiler, built on Verifereum.
- [Solidity-HOL](https://github.com/verifereum/solidity-hol): the beginnings of a Solidity semantics in HOL4.
- [HOL4](https://hol-theorem-prover.org): the theorem prover everything here is written in.
