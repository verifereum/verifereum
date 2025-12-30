Theory vfmTestDefs1951[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/RevertPrecompiledTouch_nonce.json";
val defs = mapi (define_test "1951") tests;
