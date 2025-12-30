Theory vfmTestDefs1914[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/returndatasize_after_successful_callcode.json";
val defs = mapi (define_test "1914") tests;
