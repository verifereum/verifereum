Theory vfmTestDefs1895[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/returndatacopy_after_revert_in_staticcall.json";
val defs = mapi (define_test "1895") tests;
