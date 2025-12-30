Theory vfmTestDefs0804[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/CreateMessageReverted.json";
val defs = mapi (define_test "0804") tests;
