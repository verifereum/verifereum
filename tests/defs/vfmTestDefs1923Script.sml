Theory vfmTestDefs1923[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stReturnDataTest/tooLongReturnDataCopy.json";
val defs = mapi (define_test "1923") tests;
