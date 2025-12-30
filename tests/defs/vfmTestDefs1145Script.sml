Theory vfmTestDefs1145[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/mload32bitBound_return2.json";
val defs = mapi (define_test "1145") tests;
