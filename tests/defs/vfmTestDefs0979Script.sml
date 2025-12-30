Theory vfmTestDefs0979[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stEIP2930/coinbaseT2.json";
val defs = mapi (define_test "0979") tests;
