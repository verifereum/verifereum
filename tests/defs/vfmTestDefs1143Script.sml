Theory vfmTestDefs1143[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/mload32bitBound_Msize.json";
val defs = mapi (define_test "1143") tests;
