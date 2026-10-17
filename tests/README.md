# EEST conformance tests

Verifereum is checked against the [Ethereum Execution Spec Tests
(EEST)](https://github.com/ethereum/execution-specs): every Osaka
`blockchain_test` fixture is run through the executable semantics inside
HOL4, and the outcome of each test case is recorded. The current status is
published on the [progress page](https://verifereum.org/table.html).

A full run takes many hours, so the suite is not part of CI.

## Contents

- `defs/vfmTestDefsNNNNScript.sml`: one theory per fixture json file,
  defining the test cases in that file.
- `results/vfmTestNNNNScript.sml`: one theory per fixture json file,
  running its test cases and writing one `resultNNNN_K.nsv` per case.
- `runtests.exe`: the driver. It fetches the fixtures, generates the
  scripts in `defs/` and `results/`, builds the results theories, and writes
  `results/table.html` from the `.nsv` files.
- `serial-first.txt`: the tests the driver builds one at a time before the
  rest (see [Serial-first tests](#serial-first-tests)).

`NNNN` is a test's index: the position of its json path in the sorted list
of Osaka blockchain tests in the fixtures' `.meta/index.json`. Indices are
reassigned whenever the fixtures change, so refer to a test by its json path
in anything meant to outlast a release.

## Fixtures

The EEST release is `fixtures_version` in `vfmTestAuxLib.sml` (currently
21.0.1, which has 2449 Osaka blockchain test files with 17550 cases). When
`fixtures/version.txt` does not match it, `runtests.exe` downloads
`fixtures.tar.gz` from the `tests@v<version>` release of
ethereum/execution-specs (about 1 GB) and extracts it into `fixtures/`
(about 14 GB). Both are ignored by git; delete them when you no longer need
them.

## Running

Build the driver from the repository root, then run it from `tests/`:

```bash
holbuild executable runtests
cd tests
./runtests.exe              # all tests
./runtests.exe 0135 0138    # only these indices
```

Runs resume: a results theory that is already built is not rebuilt, so
rerunning after an interruption continues where it stopped. Options:

| Option | Effect |
| --- | --- |
| `-g`, `--generate` | only fetch the fixtures and regenerate `defs/` and `results/` |
| `-f`, `--fresh` | rerun the selected tests instead of resuming |
| `-t secs`, `--time secs` | time limit per test case (default 60, or `VFM_TIME_LIMIT`) |
| `-o opt`, `--option opt` | pass `opt` to the build backend, e.g. `-o -j8` |
| `-b holbuild\|holmake`, `--backend` | build backend (default holbuild) |
| `--no-serial-first` | build all tests together (see below) |
| `-r`, `--results` | only write `results/table.html` |
| `-n`, `--noresults` | do not write `results/table.html` |

## Serial-first tests

A few tests use far more memory than the rest. Built in parallel alongside
other tests they can exhaust memory on the machine, killing the run, so
`./runtests.exe` with no indices builds them first, one at a time (`-j1`),
and then builds the remaining tests with the given options. If the
serial-first phase fails, the run stops there. `--no-serial-first` skips the
phase and builds everything together; explicit indices are always built as
given. The serial-first phase applies to the holbuild backend only.

The tests are listed by json path, relative to `fixtures/`, in
`serial-first.txt`. The driver resolves each path to its current index, and
a path that is not in the fixtures' index is an error, so a release that
drops or renames one of these files stops the run rather than silently
running it in parallel.

The current list, with its indices at 21.0.1:

| Index | Json path (under `blockchain_tests/for_osaka/`) |
| --- | --- |
| 0258 | `osaka/eip7825_transaction_gas_limit_cap/tx_gas_limit/tx_gas_limit_cap_access_list_with_diff_addr.json` |
| 0259 | `osaka/eip7825_transaction_gas_limit_cap/tx_gas_limit/tx_gas_limit_cap_access_list_with_diff_keys.json` |
| 0279 | `osaka/eip7934_block_rlp_limit/max_block_rlp_size/block_at_rlp_limit_with_logs.json` |
| 0280 | `osaka/eip7934_block_rlp_limit/max_block_rlp_size/block_at_rlp_limit_with_withdrawals.json` |
| 0281 | `osaka/eip7934_block_rlp_limit/max_block_rlp_size/block_at_rlp_size_limit_boundary.json` |
| 0282 | `osaka/eip7934_block_rlp_limit/max_block_rlp_size/block_rlp_size_at_limit_with_all_typed_transactions.json` |
| 0984 | `ported_static/stPreCompiledContracts/precomps_eip2929_cancun/precomps_eip2929_cancun.json` |
| 2263 | `prague/eip2537_bls_12_381_precompiles/bls12_g2msm/valid.json` |
| 2327 | `prague/eip7623_increase_calldata_cost/transaction_validity/transaction_validity_type_4.json` |
| 2335 | `prague/eip7702_set_code_tx/gas/intrinsic_gas_cost.json` |

The list and the timings below come from full runs at 20.0.2 ([#95
(comment)](https://github.com/verifereum/verifereum/issues/95#issuecomment-5558158839),
[#95
(comment)](https://github.com/verifereum/verifereum/issues/95#issuecomment-5734671445)).
In one run the serial-first phase took about 2h50m and the rest, at `-j8`,
about 10h. The slowest serial-first tests were `precomps_eip2929_cancun.json`
(about 62 minutes), `bls12_g2msm/valid.json` (48 minutes) and
`transaction_validity_type_4.json` (28 minutes). Some other tests are slow
but not memory-heavy, so they are not in the list.

## Updating to a new EEST release

1. Set `fixtures_version` in `vfmTestAuxLib.sml` to the new release.
2. Rebuild the driver and run `./runtests.exe -g`; commit the regenerated
   `defs/` and `results/`. Nearly every index shifts.
3. Check that every path in `serial-first.txt` still exists in the new
   fixtures (a full run fails on one that does not), and update the index
   table above.
