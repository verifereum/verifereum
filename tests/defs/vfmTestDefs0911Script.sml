Theory vfmTestDefs0911[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150Specific/NewGasPriceForCodes.json";
val defs = mapi (define_test "0911") tests;
