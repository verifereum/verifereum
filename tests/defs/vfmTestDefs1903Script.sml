Theory vfmTestDefs1903[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/returndatacopy_following_revert_in_create.json";
val defs = mapi (define_test "1903") tests;
