Theory vfmTestDefs0915[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP150Specific/Transaction64Rule_d64m1.json";
val defs = mapi (define_test "0915") tests;
