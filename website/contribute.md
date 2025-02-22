---
title: Contributing to Verifereum
header-includes:
    <link rel="icon" type="image/svg" href="./verifereum-logo-small.svg">
---

# Getting Started with [Verifereum](../)

Welcome! We're excited you're interested in contributing to Verifereum.
We're building tools for mathematical verification of Ethereum smart contracts, working closely with the HOL4 theorem prover community.

## Current Project State

Verifereum is in active early development. We're working on fundamental components like the EVM formalization while also exploring verification approaches for smart contracts. This is an exciting time to join as you can help shape the project's direction and core infrastructure.

## Getting Set Up with HOL4

Verifereum is built on [HOL4](https://hol-theorem-prover.org), and contributing often involves working with both projects.
Here's what you need to know about getting started with HOL4:

### Installation Options

1. **Building from Source (Recommended)**
   - There are detailed build instructions in the [Verifereum README](https://github.com/verifereum/verifereum?tab=readme-ov-file#getting-started)
   - Install [Poly/ML](https://polyml.org) first
   - Clone and build [HOL4](https://github.com/HOL-Theorem-Prover/HOL) from source
   - This gives you the most up-to-date version and best performance

2. **Package Managers**
   - Available for some systems but may be outdated
   - Can be useful for initial exploration
   - Consider switching to source build later

### Editor Integration

HOL4 supports several development environments - choose what works best for you:

1. **Emacs Mode**
   - Traditional and feature-rich
   - Extensive proof development support
   - Steeper learning curve
   - There is an [interaction guide](https://hol-theorem-prover.org/HOL-interaction.pdf)

2. **(Neo)vim Mode**
   - Lightweight and efficient
   - Good for those familiar with vim
   - There is a [README](https://github.com/HOL-Theorem-Prover/HOL/tree/master/tools/editor-modes/vim) for getting started

3. **VSCode Extension (Experimental)**
   - Modern interface
   - Still in development
   - Good for those new to theorem proving
   - The repository is [here](https://github.com/HOL-Theorem-Prover/hol4-vscode)

Need help with installation? Ask in [Zulip](https://hol.zulipchat.com) Verifereum channel - different approaches work better for different systems and use cases.

## Contributing to Verifereum and HOL4

Verifereum and HOL4 are tightly integrated projects. We encourage contributing to both:

- **HOL4 Contributions**
  - Improve the theorem prover infrastructure - see the [GitHub issues](https://github.com/HOL-Theorem-Prover/HOL/issues)
  - Add useful tactics and libraries
  - Fix bugs and enhance performance
  - Join the HOL4 community discussions (in the same [Zulip](https://hol.zulipchat.com))

- **Verifereum Contributions**
  - Work on EVM formalization
  - Develop verification techniques
  - Create examples and documentation
  - Help shape the project roadmap

Learning either project helps with understanding the other!

## Current Project Areas

Here are some active areas where you can contribute:

### EVM Formalization and Testing
- Adding support for EVM precompiles
  - Formalizing elliptic curve algebra for ecRecover
  - Implementing other cryptographic primitives
- Improving test coverage
  - Speeding up slow test cases
  - Adding tests from newer test suites
  - Creating focused test cases for specific features

### Verification Experiments
- Manual verification of simple contracts (e.g., WETH)
  - Understand current proof approaches
  - Identify common patterns
  - Document verification strategies
- Developing program logic for smart contracts
  - Create more abstract reasoning principles
  - Compare with direct semantic reasoning
  - Build reusable verification components

### Performance Improvements
- CakeML integration for faster execution
  - Using monadic translator for EVM semantics
  - Optimizing critical paths
  - Benchmarking and profiling

### Documentation and Examples
- Creating verification demos
  - Simple contract verifications
  - Bug-finding through proof attempts
  - Tutorial materials

## Getting Started

1. **Join the Community**
   - Introduce yourself in Zulip
   - Share your interests and background
   - Discuss potential contribution areas

2. **Set Up Development Environment**
   - Install HOL4 (see above)
   - Clone Verifereum repository
   - Try running existing proofs

3. **Find Your Focus**
   - Review current project areas
   - Look at existing issues
   - Discuss ideas in Zulip

4. **Start Contributing**
   - Begin with small improvements
   - Work with others on larger projects
   - Help develop the roadmap

## Getting Help

- Join our [Zulip](https://hol.zulipchat.com)
- Contact [Ramana (xrchz)](https://github.com/xrchz)
- Ask questions on [GitHub issues](https://github.com/verifereum/verifereum/issues)

We're building a community of people interested in formal verification of Ethereum contracts. Whether you're experienced with theorem proving or just getting started, there are ways to contribute and learn together.
