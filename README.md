# Verifereum

Prove functional correctness of Ethereum smart contracts in higher-order logic.

See [https://verifereum.org](https://verifereum.org).

When you clone this repository don't forget to `git submodule update --init` too.

Work in progress.

## Getting Started

1.  Install and build Poly/ML from source (or use a packaged version if applicable)

    i. Download the source code from the Poly/ML GitHub repository

    ```bash
    wget https://github.com/polyml/polyml/archive/refs/heads/master.zip -O poly-master.zip;
    unzip polyml-master.zip;
    ```

    ii.

    ```bash
    cd polyml-master;
    ./configure --enable-intinf-as-int;
    make -C polyml-master -j4
    make -C polyml-master install
    rm -r polyml-master polyml-master.zip
    ```

    iii. For M1 Macs you may need to edit the `/usr/local/bin/polyc` script on line line 44 and 46 to remove the quotes otherwise it'll error with `g++ -std=gnu++11: command not found`.

    >        ${LINK} ...

    instead of

    >        "${LINK}" ...

1.  Install and build HOL

    i. Download the source code from the HOL GitHub repository

    ```bash
    cd - # cd into project root
    git clone https://github.com/HOL-Theorem-Prover/HOL
    cd HOL
    poly --script tools/smart-configure.sml
    bin/build
    ```

    ii. Add the following to your `.bashrc` file

    ```bash
    cd -
    export HOLDIR=<path-to-HOL>/HOL
    export PATH=$HOLDIR/bin:$PATH
    ```

    iii. Run this to build the project and run the tests. They will take a while to run so you can cancel them.

    ```bash
    Holmake
    # Scanned 16 directories
    # Finished $(HOLDIR)/examples/json                               (0.000s)
    # vfmTypesTheory                    Documents/Code/verifereum (26s)     OK
    # vfmTransactionTheory              Documents/Code/verifereum  (2s)     OK
    # recursiveLengthPrefixTheory       Documents/Code/verifereum  (6s)     OK
    # ...
    ```

    For other tips checkout [this FAQ](https://hol-theorem-prover.org/faq.html).

In case you would rather not build the project from source, you can use Docker as described [here](docs/run-with-docker.md).

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
