Theory vfmTestDefs1110[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stMemExpandingEIP150Calls/NewGasPriceForCodesWithMemExpandingCalls.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stMemExpandingEIP150Calls/NewGasPriceForCodesWithMemExpandingCalls.json");
val defs = mapi (define_test "1110") tests;
