Theory vfmTestDefs0790[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/CREATE2_HighNonceDelegatecall.json";
val defs = mapi (define_test "0790") tests;
