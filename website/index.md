% Verifereum

# !["Verifereum logo"](verifereum-logo-big.svg "Verifereum")

## New! ☃️ Higher Order Log Cabin ☃️ Event!
- The first in-person Verifereum unconference!
- We will *hack* on + *talk* about *Verifereum*, *HOL*, *Vyper*, and *CakeML*
- We will be staying in a *beautiful venue in the Swedish countryside* for the long weekend of **February 7–10 2025** <br>
    !["Living room with fireplace (representative venue)"](venue1.png "fireplace"){ width=250px } !["Living room with couches (representative venue)"](venue2.png "couches"){ width=250px }
    !["Solarium and swimming pool (representative venue)"](venue3.png "solarium"){ width=250px } !["Cabin in the snow (representative venue)"](venue4.png "snow"){ width=250px }
- As it's the first event, accommodation and food will be covered by us (!), and you arrange your own travel ✈️
- There will be food and socialising 🔥
- All people are welcome, including folks who are just interested in the space and want to learn more 📚
- Places are limited! Please fill out **[this form](https://forms.gle/KzT7VJe2n8S1dKmN8)** to confirm attendance

## What

- Mathematical verification of Ethereum applications
- Proven functional correctness of smart contracts

## Why

- Auditing is not exhaustive; theorems rule out _all_ exploits (of a certain class)
- There is a lot of value custodied by Ethereum applications: the stakes are high for implementation bugs
- The Ethereum specification is simple, unambiguous, and easy to reason about: it is a perfect fit for formal verification

## Get involved
- Join [the CakeML Discord](https://discord.gg/a8UUs6Ce6m) and say hello in the #verifereum channel!
- Check out the [repository on GitHub](https://github.com/verifereum/verifereum)!
- Look at the open [issues](https://github.com/verifereum/verifereum/issues)
- Ask [Ramana (aka xrchz)](https://github.com/xrchz) about ideas of things to work on
- See the roadmap below for ideas

### Collaboration

Verifereum is a free software project with no legal or formal barriers to collaboration at any level of experience or commitment, as long as all results remain accessible to everyone

## Technical approach

- Formal model of the [Ethereum Virtual Machine (EVM)](https://ethereum.org/en/developers/docs/evm/) in the [HOL4 theorem prover (higher-order logic)](https://hol-theorem-prover.org)
- Operational semantics of the EVM, as a definitional interpreter
- Executable in logic
- Faithful and up to date: pass the EVM test suite, written in readable style for cross-checking against the [official specification](https://github.com/ethereum/execution-specs/)
- Program logic for verifying smart contract applications
- [Decompilation into logic](https://www.cl.cam.ac.uk/~mom22/decompilation/) and/or [compiler verification](https://cakeml.org) (e.g. for [Vyper](https://vyperlang.org)) for verifying implementations at the bytecode level

## Roadmap and status

Status: [Under heavy development](https://github.com/verifereum/verifereum/commits/main/) and seeking collaborators!

We are most of the way through the EVM base sequence

### EVM base
1. Mostly Done: Formal specification of the EVM in HOL4
   1. TODO: specify the precompiles (ecRecover, etc.)
2. Mostly Done: Make the EVM model executable (fast) in logic
3. WIP: Pass the [EVM test suite](https://github.com/ethereum/tests/)
4. TODO: Make the definitions more tidy and readable

### Decompilation track
1. TODO: Build a program logic (Hoare or Separation logic) for EVM bytecode programs
2. TODO: Verify some simple example contracts
3. TODO: Build decompilation-into-logic automation

### Verification track
1. [Started](https://github.com/xrchz/vyper-hol): Formal specification of Vyper semantics in HOL4
2. TODO: Define a copy of the compiler frontend in logic
3. TODO: ... (steps to be filled in) ...

Other tracks (bug bounties, consulting, etc.) can also be defined

## Roles needed
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
