Theory vfmTestDefs1921[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/revertRetDataSize.json";
val defs = mapi (define_test "1921") tests;
