Theory vfmTestDefs1119[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stMemoryStressTest/CALL_Bounds3.json";
val defs = mapi (define_test "1119") tests;
