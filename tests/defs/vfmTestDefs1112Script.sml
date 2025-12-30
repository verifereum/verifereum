Theory vfmTestDefs1112[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/CALLCODE_Bounds.json";
val defs = mapi (define_test "1112") tests;
