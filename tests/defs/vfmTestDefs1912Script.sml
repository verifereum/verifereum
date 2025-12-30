Theory vfmTestDefs1912[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/returndatasize_after_failing_staticcall.json";
val defs = mapi (define_test "1912") tests;
