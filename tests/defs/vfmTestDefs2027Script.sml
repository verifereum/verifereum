Theory vfmTestDefs2027[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/shl_-1_1.json";
val defs = mapi (define_test "2027") tests;
