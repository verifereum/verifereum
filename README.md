# Verifereum

Prove functional correctness of Ethereum smart contracts in higher-order logic.

See [https://verifereum.org](https://verifereum.org).

When you clone this repository don't forget to `git submodule update --init` too.

Work in progress.

## Getting Started

1. Install Docker Desktop for your platform from [here](https://docs.docker.com/desktop/).

1. Run the following command to initialize the environment and enter the shell. On its first run it'll build the image which could take a while:

```sh
docker compose run verifereum
```

1. Within the shell, run this to build the project and run the tests:

```sh
Holmake
```

## Links

- The files in this repository are intended for use with [the HOL theorem prover](https://hol-theorem-prover.org).
- An official executable specification of the Ethereum virtual machine can be found [here](https://github.com/ethereum/execution-specs).
- Another useful resources on the EVM is [evm.codes](https://evm.codes).

## Plan

- Define the machine
- Pass existing [test](https://github.com/ethereum/tests) [suites](https://github.com/ethereum/execution-spec-tests)
- Define a program logic (for use with [decompilation into logic](https://www.cse.chalmers.se/~myreen/decompilation.html))
- Specify and verify some simple one-contract protocols ([WETH](https://etherscan.io/address/0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2#code), [RocketSplit](https://github.com/xrchz/rocketsplit), etc.)
- ...
