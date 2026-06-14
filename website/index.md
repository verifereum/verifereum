---
title: Verifereum
header-includes:
    <link rel="icon" type="image/svg" href="./verifereum-logo-small.svg">
---

# !["Verifereum logo"](verifereum-logo-big.svg "Verifereum")

## Formal Semantics of the Ethereum Virtual Machine in HOL4

Verifereum is an open-source project centred on a comprehensive executable formal semantics of the [Ethereum](https://ethereum.org) Execution Layer's EVM, mechanised in the [HOL4 theorem prover](https://hol-theorem-prover.org). The semantics targets the live Ethereum network's current fork (Osaka) and serves as a foundation for smart contract verification, EVM program logics, and compiler verification targeting EVM bytecode.

### Why Verifereum Matters

- **Beyond Traditional Auditing**: While audits can find bugs, mathematical verification proves the absence of entire classes of vulnerabilities
- **High Stakes, Higher Standards**: With billions of dollars secured by smart contracts, formal verification offers the strongest security guarantees possible
- **Perfect Fit**: Ethereum's deterministic execution model, where additionally code is expensive so applications are small, makes it an ideal candidate for formal verification

**[→ Learn how to contribute](/contribute)**

## Project Status & Recent Achievements

- Complete, production-quality formal semantics of the EVM Execution Layer in HOL4
- Scope focused on the live Ethereum network's current fork (Osaka); the Consensus Layer is not currently in scope
- Executable semantics by evaluation inside the logic, used to run the conformance tests
- Approximately complete [Ethereum Execution Spec Tests (EEST) suite](https://eest.ethereum.org/main/consuming_tests/blockchain_test/) coverage, with detailed status tracked on the [progress page](table.html)
- Machine-checked semantic properties, including frame-style storage/account preservation theorems and gas monotonicity results
- Program logic and contract-verification infrastructure under active development
- Sister project for [Vyper](https://vyperlang.org) [semantics and compiler verification](https://github.com/verifereum/vyper-hol)
- Hosted our first community event (Higher Order Log Cabin) in February 2025, bringing together researchers and developers

## Get Involved

We welcome contributors of all experience levels!

Start by reading our [Contributor Guide](/contribute) to learn how to set up your development environment and find your first project.

### For Technical Contributors

1. **Join the Community**:
   - Connect on [Zulip](https://hol.zulipchat.com) (join the Verifereum channel)
   - Watch our [GitHub repository](https://github.com/verifereum/verifereum)

2. **Start Contributing**:
   - Check out open [issues](https://github.com/verifereum/verifereum/issues)
   - Contact [Ramana (xrchz)](https://github.com/xrchz) for project ideas
   - Review our technical documentation below

### Technical Focus Areas

We're currently working on three main tracks:

1. **EVM Semantics and Conformance**
   - Maintaining the executable HOL4 semantics for the live Ethereum fork
   - Tracking fork changes and EEST updates
   - Investigating any remaining test-suite exceptions
   - Optimizing execution by evaluation in logic

2. **Semantic Theorems and Program Logic**
   - Proving frame-style properties for storage, accounts, and call contexts
   - Developing gas and resource reasoning principles
   - Building Hoare/separation logic for EVM bytecode
   - Creating verification examples and proof automation

3. **Compiler Verification**
   - Supporting EVM bytecode as a verified compiler target
   - Developing Vyper semantics and compiler verification in the Vyper-HOL sister project
   - Building reusable compiler-correctness infrastructure

## Technical Details

### Our Approach

- **Foundation**: Executable formal semantics of the Ethereum Execution Layer's EVM in HOL4 (Higher-Order Logic)
- **Methodology**: Operational semantics via definitional interpreter
- **Validation**: Approximately complete EEST coverage, with detailed status tracked publicly
- **Verification**: Semantic theorems and program logic for smart contract correctness proofs
- **Implementation**: Focus on proof-producing reasoning, decompilation, and compiler verification

### Collaboration Philosophy

Verifereum is committed to open collaboration and [free software](https://fsf.org) principles.
All our work remains accessible to everyone, and we welcome contributions at any level of experience or commitment.

## Looking to Contribute?

See our [detailed contributor guide](/contribute) to get started.

We have opportunities for both technical and non-technical contributions:

### Technical Roles
- Formal specification development
- HOL4 theorem proving
- Proof automation infrastructure
- Technical documentation
- Example contract verification

### Social Roles
- Documentation improvement
- Community building
- Project management
- Grant writing and fundraising

Ready to start? Join our [Zulip](https://hol.zulipchat.com) and check out our [contributor guide](/contribute)!
