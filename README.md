# verifereum
Prove functional correctness of Ethereum smart contracts in higher-order logic.

Work in progress.

## Links
* The files in this repository are intended for use with [the HOL theorem prover](https://hol-theorem-prover.org).
* An official executable specification of the Ethereum virtual machine can be found [here](https://github.com/ethereum/execution-specs).
* Another useful resources on the EVM is [evm.codes](https://evm.codes).

## Plan
* Define the machine
* Pass existing [test](https://github.com/ethereum/tests) [suites](https://github.com/ethereum/execution-spec-tests)
* Define a program logic (for use with [decompilation into logic](https://www.cse.chalmers.se/~myreen/decompilation.html))
* Specify and verify some simple one-contract protocols ([WETH](https://etherscan.io/address/0xc02aaa39b223fe8d0a0e5c4f27ead9083c756cc2#code), [RocketSplit](https://github.com/xrchz/rocketsplit), etc.)
* ...
