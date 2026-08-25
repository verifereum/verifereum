Theory vfmTestDefs0911[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stEIP150Specific/NewGasPriceForCodes.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stEIP150Specific/NewGasPriceForCodes.json");
val defs = mapi (define_test "0911") tests;
