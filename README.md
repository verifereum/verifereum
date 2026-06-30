![Verifereum](website/verifereum-logo-big.svg)

[![License: GPL v3](https://img.shields.io/badge/License-GPLv3-blue.svg)](https://www.gnu.org/licenses/gpl-3.0)
[![Website](https://img.shields.io/badge/website-verifereum.org-brightgreen)](https://verifereum.org)
[![Zulip](https://img.shields.io/badge/chat-Zulip-blue)](https://hol.zulipchat.com)

**A production-quality executable formal semantics of the Ethereum Virtual Machine in higher-order logic.**

Verifereum is an open-source project centred on a comprehensive formal semantics of the Ethereum Execution Layer's EVM, mechanised in the [HOL4 theorem prover](https://hol-theorem-prover.org). The semantics is executable by evaluation inside the logic and is designed as a foundation for smart contract verification, EVM program logics, and compiler verification targeting EVM bytecode.

## Why Verifereum?

- **Beyond Traditional Auditing**: While audits can find bugs, mathematical verification proves the *absence* of entire classes of vulnerabilities
- **High Stakes, Higher Standards**: With billions of dollars secured by smart contracts, formal verification offers the strongest security guarantees possible
- **Perfect Fit**: Ethereum's deterministic execution model, where code is expensive so applications are small, makes it an ideal candidate for formal verification

## Current Status

Verifereum contains a complete, production-quality formal semantics of the EVM Execution Layer in HOL4. It targets the live Ethereum network's current fork (Osaka); the Consensus Layer is not currently in scope.

The semantics is executable in the logic. This is not intended to be a fast EVM implementation, but it is how we run the conformance tests: Verifereum has approximately complete coverage of the [Ethereum Execution Spec Tests (EEST)](https://eest.ethereum.org/main/consuming_tests/blockchain_test/), with detailed status tracked on the [progress page](https://verifereum.org/table.html).

Beyond executable specification and test-suite validation, the repository contains machine-checked theorems about the semantics. The proof library includes frame-style theorems showing that EVM execution only mutates storage, transient storage, code, and nonce in the accounts and slots it is allowed to touch, plus gas monotonicity theorems showing that consumed gas in a frame only increases through execution, including across CALL/CREATE structure. These results support program verification and program-logic developments for EVM bytecode.

Other active directions include:

- Program logic and proof infrastructure in `prog/`
- Example and experimental contract-verification developments in `examples/`
- Support for compiler verification targeting the EVM
- The sister project [Vyper-HOL](https://github.com/verifereum/vyper-hol), developing Vyper semantics and compiler verification

## Project Structure

```
verifereum/
├── spec/           # Formal EVM specification
│   ├── vfmExecutionScript.sml    # EVM execution semantics
│   ├── vfmOperationScript.sml    # EVM operations
│   ├── vfmStateScript.sml        # EVM state model
│   └── prop/                     # Properties and proofs about EVM
├── prog/           # Program logic for verification
├── util/           # Utilities (RLP, Merkle Patricia Trie, crypto primitives)
│   ├── recursiveLengthPrefixScript.sml
│   ├── merklePatriciaTrieScript.sml
│   ├── secp256k1Script.sml
│   └── contractABIScript.sml
├── examples/       # Example contract verifications
│   └── wrappedEtherScript.sml    # WETH contract verification
├── tests/          # EVM test suite
├── website/        # Project website source
└── docs/           # Documentation
```

## Getting Started

Verifereum is developed in the [HOL4](https://hol-theorem-prover.org) theorem prover, which is written in Standard ML, and is built with [`holbuild`](https://github.com/charles-cooper/holbuild). The repository's `holproject.toml` is the source of truth for the project configuration and pinned HOL dependencies. The CI workflow (`.github/workflows/holbuild.yml`) is the recommended reference for the exact automated build.

For a local build, install `holbuild` v0.8.1 and run:

```bash
holbuild buildhol
holbuild -j"$(nproc)" build
```

`holbuild buildhol` builds and caches the HOL toolchain and dependencies specified by `holproject.toml`.

Plain `Holmake` remains supported as a secondary check when a compatible HOL4 installation is already available, and is also checked in CI.

Release instructions, including the prebuilt holbuild archive artefact, are in [docs/release.md](docs/release.md).

## Contributing

We welcome contributors of all experience levels! See the [contributor guide](https://verifereum.org/contribute) for details on:

- Setting up your development environment
- Current project areas (EVM formalisation, verification experiments, performance improvements)
- Editor integration (Emacs, Vim, VSCode, Kakoune)

**Get involved:**
- Join us on [Zulip](https://hol.zulipchat.com) (Verifereum channel)
- Check [open issues](https://github.com/verifereum/verifereum/issues)
- Contact [Ramana (xrchz)](https://github.com/xrchz)

## Related Resources

- [HOL Theorem Prover](https://hol-theorem-prover.org)
- [Ethereum Execution Specs](https://github.com/ethereum/execution-specs) - Official Python EVM specification
- [evm.codes](https://evm.codes) - EVM opcode reference
- [Vyper-HOL](https://github.com/verifereum/vyper-hol) - Vyper semantics in HOL4

## License

Verifereum is free software, released under the [GNU General Public License v3](LICENSE).
