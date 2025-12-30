Theory vfmTestDefs2021[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/shl01-0101.json";
val defs = mapi (define_test "2021") tests;
