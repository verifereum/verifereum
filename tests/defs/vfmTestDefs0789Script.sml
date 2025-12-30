Theory vfmTestDefs0789[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/CREATE2_HighNonce.json";
val defs = mapi (define_test "0789") tests;
