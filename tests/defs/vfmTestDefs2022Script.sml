Theory vfmTestDefs2022[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/shl01-ff.json";
val defs = mapi (define_test "2022") tests;
