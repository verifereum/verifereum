Theory vfmTestDefs1144[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/mload32bitBound_return.json";
val defs = mapi (define_test "1144") tests;
