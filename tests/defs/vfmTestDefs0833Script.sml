Theory vfmTestDefs0833[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/returndatacopy_following_successful_create.json";
val defs = mapi (define_test "0833") tests;
