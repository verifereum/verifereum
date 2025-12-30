Theory vfmTestDefs2026[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/shl_-1_0.json";
val defs = mapi (define_test "2026") tests;
