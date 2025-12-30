Theory vfmTestDefs1892[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/returndatacopy_after_failing_callcode.json";
val defs = mapi (define_test "1892") tests;
