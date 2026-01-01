![Verifereum](website/verifereum-logo-big.svg)

[![License: GPL v3](https://img.shields.io/badge/License-GPLv3-blue.svg)](https://www.gnu.org/licenses/gpl-3.0)
[![Website](https://img.shields.io/badge/website-verifereum.org-brightgreen)](https://verifereum.org)
[![Zulip](https://img.shields.io/badge/chat-Zulip-blue)](https://hol.zulipchat.com)

**Prove functional correctness of Ethereum smart contracts in higher-order logic.**

Verifereum is an open-source project that brings mathematical rigour to Ethereum smart contract verification. Using the [HOL4 theorem prover](https://hol-theorem-prover.org), we're building tools to prove the correctness of smart contracts and eliminate entire classes of vulnerabilities.

## Why Verifereum?

- **Beyond Traditional Auditing**: While audits can find bugs, mathematical verification proves the *absence* of entire classes of vulnerabilities
- **High Stakes, Higher Standards**: With billions of dollars secured by smart contracts, formal verification offers the strongest security guarantees possible
- **Perfect Fit**: Ethereum's deterministic execution model, where code is expensive so applications are small, makes it an ideal candidate for formal verification

## Current Status

- Formal specification of EVM operations in HOL4
- [Progress](https://verifereum.org/table.html) on passing the [Ethereum Execution Spec Tests (EEST)](https://eest.ethereum.org/main/consuming_tests/blockchain_test/)
- Work-in-progress verification of [WETH contract](https://etherscan.io/address/0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2#code) (see `examples/wrappedEtherScript.sml`)
- [Vyper language semantics and compiler verification](https://github.com/verifereum/vyper-hol) underway

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

Verifereum is developed in the [HOL4](https://hol-theorem-prover.org) theorem prover, which is written in Standard ML.

### Option 1: Build from Source

1. **Install Poly/ML** (you may prefer to use a packaged version if available)

    ```bash
    curl -L https://github.com/polyml/polyml/archive/refs/heads/master.zip | bsdtar -xf -
    cd polyml-master
    ./configure --enable-intinf-as-int
    make -j4
    make install
    cd ..
    rm -r polyml-master
    ```

2. **Build HOL4**

    ```bash
    git clone https://github.com/HOL-Theorem-Prover/HOL
    cd HOL
    poly --script tools/smart-configure.sml
    bin/build
    ```

    Add to your `.bashrc`:
    ```bash
    export HOLDIR=<path-to-HOL>/HOL
    export PATH=$HOLDIR/bin:$PATH
    ```

3. **Clone and Build Verifereum**

    ```bash
    git clone https://github.com/verifereum/verifereum
    cd verifereum
    Holmake
    ```

### Option 2: Use Docker

See [docs/run-with-docker.md](docs/run-with-docker.md) for instructions on running with Docker.

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
