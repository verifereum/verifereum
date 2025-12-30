Theory vfmTestDefs1920[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/returndatasize_initial_zero_read.json";
val defs = mapi (define_test "1920") tests;
