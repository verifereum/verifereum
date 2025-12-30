Theory vfmTestDefs1017[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/extCodeHashDeletedAccount2.json";
val defs = mapi (define_test "1017") tests;
