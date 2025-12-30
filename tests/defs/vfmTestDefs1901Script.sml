Theory vfmTestDefs1901[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/returndatacopy_following_failing_call.json";
val defs = mapi (define_test "1901") tests;
