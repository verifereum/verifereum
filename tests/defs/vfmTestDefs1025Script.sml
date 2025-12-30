Theory vfmTestDefs1025[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/extCodeHashNewAccount.json";
val defs = mapi (define_test "1025") tests;
