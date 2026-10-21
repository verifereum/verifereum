# EEST conformance tests

Verifereum is checked against the [Ethereum Execution Spec Tests
(EEST)](https://github.com/ethereum/execution-specs): every Osaka
`blockchain_test` fixture is run through the executable semantics inside
HOL4, and the outcome of each test case is recorded. The current status is
published on the [progress page](https://verifereum.org/table.html).

The proof-producing runner takes many hours, so CI uses the unchecked native runner.

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
| `-o opt`, `--option opt` | pass `opt` to the build backend, e.g. `-o -j8` (see also [Heap cap](#heap-cap)) |
| `-b holbuild\|holmake`, `--backend` | build backend (default holbuild) |
| `--no-serial-first` | build all tests together (see below) |
| `-r`, `--results` | only write the results table |
| `-n`, `--noresults` | do not write the results table |
| `--table file` | write the results table to `results/file` (default `table.html`) |

Each distinct genesis state root in a fixture file is proved once and reused
by every case that shares it. The time limit applies separately to proving a
root and to evaluating each case; a root that times out makes every case
sharing it a `Timeout`.

## Unchecked native runner

`runtests_unchecked.sml` runs the same fixture checks using EmitML-generated
Standard ML, without building fixture theories or producing result theorems.
The exporter uses the existing CV-translated equations of `run_test`, including
their executable state representations; it does not reimplement EVM execution.
The native runtime supplies arbitrary-precision CV arithmetic and maps translated
word AND, OR, XOR, and exponentiation operations to Poly/ML primitives. The
exporter hoists generated numeral literals so each distinct value is parsed once.
The generated evaluator validates the parent-derived excess blob gas before
transactions, so an invalid header cannot force evaluation of its blob base fee.
The fixture adapter reuses the certified JSON parser without constructing HOL terms.

Build from the repository root:

```bash
holbuild build vfmUncheckedEmitTheory
holbuild executable runtests_unchecked
cd tests
./runtests_unchecked.exe -j8             # all fixtures
./runtests_unchecked.exe -j2 0135 0138    # selected fixture indices
./runtests_unchecked.exe -f -t300 0135   # rerun with a longer timeout
```

The first command creates the ignored `vfmUncheckedML.sml` and `.sig` files;
run it before the first executable build in a clean checkout. Subsequent
executable builds depend on the exporter so changes to the semantics regenerate
the evaluator. Plain `Holmake runtests_unchecked.exe` from `tests/` also has
generation rules.

The runner supports `-h`, `-r`, `-n`, `-f`, `-t`, `--table`, and `--no-serial-first` with
the corresponding meanings above. Use `-j N` / `--jobs N` for worker concurrency
(default 1). There is no build backend or per-fixture script generation, so
`-b`, `-o`, and `-g` do not apply. Each fixture runs in a fresh worker process;
the full-suite serial-first policy remains enabled by default. Workers run
with `--gcthreads 1`: with Poly/ML 5.9.2's default parallel GC, the worker for
the 25 MB `tx_gas_limit_cap_full_calldata.json` intermittently dies with `Run
out of store` while parsing it.

The per-case timeout covers native input encoding and execution, but not JSON
parsing or worker startup. It defaults to 60 seconds and reads `VFM_TIME_LIMIT`
when the executable runs; `-t` overrides it. Completed cases resume individually,
including recorded timeouts. Use `-f` to rerun them after changing the limit.
Cases are rerun when their result file predates the executable, fixture JSON,
or fixture version file. Result files are published atomically.

Both runners write the same `results/resultNNNN_K.nsv` files and the same
results table (see [Results](#results)), and each result records which runner
produced it. Results from one runner can therefore replace or be resumed by the
other; use `-f` to force execution by the selected runner. Neither runner's
successful exit status guarantees that every case passed: inspect the report
for mismatches and timeouts.
Parser errors, worker failures, and invalid command options cause the native
runner to exit unsuccessfully.

### GitHub CI

The `holbuild` GitHub Actions workflow builds `runtests_unchecked.exe` and runs
the complete suite from a clean result set with one fixture worker per available
CPU. The per-case timeout remains 60 seconds. Extracted fixtures are cached by
platform and fixture-definition version to avoid downloading and unpacking the
release on every run.

Each run writes status counts and measured wall, user, system, and peak-memory
figures to the GitHub job summary. The `eest-results-<commit>-<attempt>` artifact
contains every `.nsv` result, `table.html`, and the timing file for 30 days.
Expect approximately two to three hours on a standard GitHub-hosted runner.

## Results

Each test case's result is a file `results/resultNNNN_K.nsv`, where `K` is the
case's position in its fixture file. Its lines are the case's name, its result
(`Passed`, `Timeout`, or what went wrong), the seconds it took, and the runner
that produced it: `checked` for the results theories of `runtests.exe`,
`unchecked` for `runtests_unchecked.exe`. Files written before runners recorded
themselves have only the first three lines, and their runner is `unknown`. If
you know a directory of them is all checked, label them so:

```bash
for f in results/result*.nsv; do [ "$(wc -l < "$f")" = 3 ] && echo checked >> "$f"; done
```

The results table lists every `.nsv` file in `results/` with its runner, and its
header says whether the results are `checked`, `unchecked`, `unknown`, or mixed,
with the count of each. It is written to `results/table.html`, or to another
file there with `--table`, next to the `table.css` and `table.js` it uses. For
checked and unchecked tables side by side, run `./runtests.exe`, which writes
`table.html`, and then `./runtests_unchecked.exe -f --table
table-unchecked.html`; `-f` makes the second runner rerun every case rather
than resume from the first runner's results. The second run replaces the first
runner's result files, so `table.html` can no longer be rewritten from them;
copy `results/*.nsv` first if you need them again.

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

## Heap cap

Poly/ML grows a process's heap well past its live data when nothing caps
it, so even built alone, one test can take all the machine's memory. With
the holbuild backend, `./runtests.exe` therefore passes `--max-heap=24000`
to holbuild, which caps the heap of each test it builds at 24000 MB. To use
another cap, pass your own, e.g. `./runtests.exe -o --max-heap=32000`; `-o`
takes a single argument, so use the `=` form.

Use `--max-heap`, not `--maxheap`: holbuild's own Poly/ML runtime consumes
`--maxheap`, which then caps holbuild rather than the tests
([HOL-Theorem-Prover/holbuild#237](https://github.com/HOL-Theorem-Prover/holbuild/issues/237)).

At 21.0.1, `intrinsic_gas_cost.json` grew past 55 GB without a cap, and
built in about the same time with any cap from 16000 to 50000 MB. With
8000 MB it made no progress in 18 minutes, spending its time in garbage
collection.

## Updating to a new EEST release

1. Set `fixtures_version` in `vfmTestAuxLib.sml` to the new release.
2. Rebuild the driver and run `./runtests.exe -g`; commit the regenerated
   `defs/` and `results/`. Nearly every index shifts.
3. Check that every path in `serial-first.txt` still exists in the new
   fixtures (a full run fails on one that does not), and update the index
   table above.
4. After the full run, update the pass count and EEST version in the
   Status section of `website/index.md` from the new `table.html`.
