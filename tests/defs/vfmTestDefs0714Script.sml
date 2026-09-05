Theory vfmTestDefs0714[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP150singleCodeGasPrices/eip2929_oog/eip2929_oog.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP150singleCodeGasPrices/eip2929_oog/eip2929_oog.json");
val defs = mapi (define_test "0714") tests;
