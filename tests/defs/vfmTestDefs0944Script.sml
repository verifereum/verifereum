Theory vfmTestDefs0944[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stEIP150singleCodeGasPrices/RawDelegateCallGasMemoryAsk.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stEIP150singleCodeGasPrices/RawDelegateCallGasMemoryAsk.json");
val defs = mapi (define_test "0944") tests;
