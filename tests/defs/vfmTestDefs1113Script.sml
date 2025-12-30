Theory vfmTestDefs1113[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/CALLCODE_Bounds2.json";
val defs = mapi (define_test "1113") tests;
