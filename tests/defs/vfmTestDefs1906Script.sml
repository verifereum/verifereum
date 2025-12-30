Theory vfmTestDefs1906[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/returndatacopy_initial.json";
val defs = mapi (define_test "1906") tests;
