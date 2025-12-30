Theory vfmTestDefs1896[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/returndatacopy_after_successful_callcode.json";
val defs = mapi (define_test "1896") tests;
