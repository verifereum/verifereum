Theory vfmTestDefs0834[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/returndatasize_following_successful_create.json";
val defs = mapi (define_test "0834") tests;
