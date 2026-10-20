---
title: Contributing to Verifereum
lang: en
description: How to build Verifereum, set up an editor for HOL4, and find something to work on.
header-includes:
    <link rel="icon" type="image/svg" href="./verifereum-logo-small.svg">
---

# Contributing to [Verifereum](../)

Verifereum is an executable formal semantics of the Ethereum Virtual Machine in the [HOL4](https://hol-theorem-prover.org) theorem prover, with machine-checked theorems and a program logic built on it. Contributing means writing HOL4 definitions and proofs, or Standard ML for the tooling around them. This page covers getting a build, setting up an editor, and where help is welcome.

## Building

Verifereum is built with [holbuild](https://github.com/charles-cooper/holbuild), which fetches and builds the pinned HOL4 version for you, so there is no HOL4 to install first; you need [Poly/ML](https://polyml.org) and git. The version of holbuild to install is `minimum_version` in [`holproject.toml`](https://github.com/verifereum/verifereum/blob/main/holproject.toml), which also pins HOL4 and the project's dependencies. Then, in a clone of the [repository](https://github.com/verifereum/verifereum):

```bash
holbuild buildhol          # build the HOL4 toolchain (once)
holbuild -j"$(nproc)" build
```

The [README](https://github.com/verifereum/verifereum#getting-started) has the details, and the CI workflow in `.github/workflows/` is the exact build to compare against. Running the Ethereum conformance tests is a separate, many-hour job described in [`tests/README.md`](https://github.com/verifereum/verifereum/blob/main/tests/README.md).

## Editor integration

HOL4 proofs are developed interactively, sending goals and tactics from the editor to a running HOL session. HOL4 ships modes for:

- Emacs: the most complete; see the [interaction guide](https://hol-theorem-prover.org/HOL-interaction.pdf).
- Vim and Neovim: see the [README](https://github.com/HOL-Theorem-Prover/HOL/tree/develop/tools/editor-modes/vim).
- Kakoune: see the [README](https://github.com/HOL-Theorem-Prover/HOL/tree/develop/tools/editor-modes/kak).
- VS Code: the [hol4-vscode](https://github.com/HOL-Theorem-Prover/hol4-vscode) extension, still experimental.

Ask in the [Verifereum channel](https://hol.zulipchat.com/#narrow/channel/verifereum) on the HOL Zulip if setup gives you trouble; different approaches work better on different systems.

## Where help is welcome

The [open issues](https://github.com/verifereum/verifereum/issues) are the current to-do list. The broad areas:

- Keeping the semantics current: each Ethereum fork changes the EVM, and the next one, Glamsterdam, is coming. Tracking the execution spec and the test suite releases is ongoing work.
- Conformance test exceptions: the tests that don't pass yet are mostly timeouts in evaluation inside the logic. Making evaluation faster, or finding why a test is slow, moves the pass rate.
- Theorems about the semantics: frame theorems, gas accounting, and invariants of execution, in `spec/prop/`. Many instructions and cases still lack them.
- Program logic and verified contracts: the separation logic in `prog/` and the WETH example in `examples/` are the start. More examples are wanted, and the proof automation they call for.
- Faster execution: a proof-producing translation of the semantics to [CakeML](https://cakeml.org) ([issue #14](https://github.com/verifereum/verifereum/issues/14)).
- HOL4 itself: Verifereum stresses the prover, and improvements to HOL4's libraries and evaluation help everyone; its [issues](https://github.com/HOL-Theorem-Prover/HOL/issues) are open too.

If you are new to HOL4, start by building the project and stepping through an existing proof in your editor, then pick a small issue and say in Zulip that you are on it.

## Getting help

- The [Verifereum channel](https://hol.zulipchat.com/#narrow/channel/verifereum) on the HOL Zulip, which is also where the HOL4 community is.
- [GitHub issues](https://github.com/verifereum/verifereum/issues).
- [Ramana (xrchz)](https://github.com/xrchz), who leads the project.
