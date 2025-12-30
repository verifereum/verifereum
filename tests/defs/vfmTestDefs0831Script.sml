Theory vfmTestDefs0831[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/returndatacopy_following_create.json";
val defs = mapi (define_test "0831") tests;
