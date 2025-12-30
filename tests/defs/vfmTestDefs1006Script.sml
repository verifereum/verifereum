Theory vfmTestDefs1006[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/extCodeHashCALL.json";
val defs = mapi (define_test "1006") tests;
