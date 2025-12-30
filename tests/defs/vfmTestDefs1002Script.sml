Theory vfmTestDefs1002[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/createEmptyThenExtcodehash.json";
val defs = mapi (define_test "1002") tests;
