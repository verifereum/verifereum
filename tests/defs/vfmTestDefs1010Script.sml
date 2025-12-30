Theory vfmTestDefs1010[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stExtCodeHash/extCodeHashCreatedAndDeletedAccountCall.json";
val defs = mapi (define_test "1010") tests;
