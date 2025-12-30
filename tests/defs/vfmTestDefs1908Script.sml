Theory vfmTestDefs1908[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/returndatacopy_initial_big_sum.json";
val defs = mapi (define_test "1908") tests;
