---
title: Verifereum
header-includes:
    <link rel="icon" type="image/svg" href="./verifereum-logo-small.svg">
---

# !["Verifereum logo"](verifereum-logo-big.svg "Verifereum")

## Mathematically Verified Ethereum Smart Contracts

Verifereum is an open-source project that brings mathematical rigour to [Ethereum](https://ethereum.org) smart contract verification.
Using the [HOL4 theorem prover](https://hol-theorem-prover.org), we're building tools to prove the correctness of smart contracts and eliminate entire classes of vulnerabilities.

### Why Verifereum Matters

- **Beyond Traditional Auditing**: While audits can find bugs, mathematical verification proves the absence of entire classes of vulnerabilities
- **High Stakes, Higher Standards**: With billions of dollars secured by smart contracts, formal verification offers the strongest security guarantees possible
- **Perfect Fit**: Ethereum's deterministic execution model, where additionally code is expensive so applications are small, makes it an ideal candidate for formal verification

**[→ Learn how to contribute](/contribute)**

## Project Status & Recent Achievements

- Active development with regular commits to our [main repository](https://github.com/verifereum/verifereum)
- Completed formal specification of most EVM operations in HOL4
- Hosting our first community event (Higher Order Log Cabin) in February 2025, bringing together researchers and developers
- Making progress on [Vyper](https://vyperlang.org) [semantics formalization](https://github.com/xrchz/vyper-hol)

## Get Involved

We welcome contributors of all experience levels!

Start by reading our [Contributor Guide](/contribute) to learn how to set up your development environment and find your first project.

### For Technical Contributors

1. **Join the Community**:
   - Connect on [Discord](https://discord.gg/a8UUs6Ce6m) (join the #verifereum channel)
   - Watch our [GitHub repository](https://github.com/verifereum/verifereum)

2. **Start Contributing**:
   - Check out open [issues](https://github.com/verifereum/verifereum/issues)
   - Contact [Ramana (xrchz)](https://github.com/xrchz) for project ideas
   - Review our technical documentation below

### Technical Focus Areas

We're currently working on three main tracks:

1. **EVM Base Layer**
   - Refining our formal EVM specification
   - Implementing precompiles (ecRecover, etc.)
   - Optimizing execution in logic
   - Ensuring test suite compliance

2. **Decompilation Pipeline**
   - Building Hoare/Separation logic for EVM bytecode
   - Creating verification examples
   - Developing decompilation automation

3. **Vyper Verification**
   - Formalizing Vyper semantics
   - Implementing compiler frontend in logic
   - Building verification infrastructure

## Technical Details

### Our Approach

- **Foundation**: Formal model of the EVM in HOL4 (Higher-Order Logic)
- **Methodology**: Operational semantics via definitional interpreter
- **Validation**: Complete EVM test suite compliance
- **Verification**: Program logic for smart contract correctness proofs
- **Implementation**: Focus on decompilation and compiler verification

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

Ready to start? Join our [Discord](https://discord.gg/a8UUs6Ce6m) and check out our [contributor guide](/contribute)!
