Theory vfmTestDefs1893[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/returndatacopy_after_failing_delegatecall.json";
val defs = mapi (define_test "1893") tests;
