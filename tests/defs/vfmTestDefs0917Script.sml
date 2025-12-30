Theory vfmTestDefs0917[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150Specific/Transaction64Rule_integerBoundaries.json";
val defs = mapi (define_test "0917") tests;
