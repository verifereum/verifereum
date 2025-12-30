Theory vfmTestDefs1898[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/returndatacopy_after_successful_staticcall.json";
val defs = mapi (define_test "1898") tests;
