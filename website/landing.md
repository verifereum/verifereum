# What is it?

- Mathematical verification of Ethereum applications
- Proven functional correctness of smart contracts

## Technical ideas

- Formal model of the [Ethereum Virtual Machine (EVM)](https://ethereum.org/en/developers/docs/evm/) in the [HOL4 theorem prover (higher-order logic)](https://hol-theorem-prover.org)
- Operational semantics of the EVM, as a definitional interpreter
- Executable in logic
- Faithful and up to date: pass the EVM test suite, written in readable style for cross-checking against the official specification
- Program logic for verifying smart contract applications
- [Decompilation into logic](https://www.cl.cam.ac.uk/~mom22/decompilation/) and/or [compiler verification](https://cakeml.org) (e.g. for [Vyper](https://vyperrlang.org)) for verifying implementations at the bytecode level

# Why this project?

- Auditing is not exhaustive; with a theorem you can rule out _all_ exploits (of a certain class)
- There is a lot of value custodied by Ethereum applications: the stakes are high for implementation bugs
- The Ethereum specification is simple, unambiguous, and easy to reason about: it is a perfect fit for formal verification

# Get involved
- Join [the CakeML Discord](https://discord.gg/a8UUs6Ce6m) and say hello in the #verifereum channel!
- Check out the [repository on GitHub](https://github.org/verifereum/verifereum)!
- Ask [Ramana (aka xrchz)](https://github.com/xrchz) about ideas of things to work on
- See the roadmap below for ideas

## Approach to collaboration

Verifereum is a free software project with no legal or formal barriers to collaboration at any level of experience or commitment, as long as all results remain accessible to everyone.

# Roadmap and status

Status: Under heavy development and seeking collaborators!

We are most of the way through the EVM base sequence

## EVM base
1. Mostly Done: Formal specification of the EVM in HOL4
   1. TODO: specify the precompiles (ecRecover, etc.)
2. Mostly Done: Make the EVM model executable (fast) in logic
3. WIP: Pass the [EVM test suite](https://github.com/ethereum/tests/)

## Decompilation track
1. TODO: Build a program logic (Hoare or Separation logic) for EVM bytecode programs
2. TODO: Verify some simple example contracts
3. TODO: Build decompilation-into-logic automation

## Verification track
1. Started: Formal specification of Vyper semantics in HOL4
2. TODO: Define a copy of the compiler frontend in logic
3. TODO: ... (steps to be filled in) ...

Other tracks (bug bounties, consulting, etc.) can also be defined

# Roles needed
- Technical contributors (i.e. interested to commit code to git repositories)
    - work on formal specifications/definitions
    - theorem proving - writing and maintaining proofs in HOL4
    - proof automation / building infrastructure for theorem proving
    - technical documentation and tutorials
    - issue curation, triaging, etc.
    - creating examples of verified applications
- Non-technical contributors (i.e. not working directly/primarily with code)
    - grant-writing and fundraising
    - recruiting/networking
    - community-building and maintenance
    - editing and styling documentation and other comms
    - project management - roadmap, milestones, priorities, checkins, etc.
    - legal + accounting + bizdev + investor relations, for any for-profit work built on top
