Theory vfmTestDefs2020[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/shl01-0100.json";
val defs = mapi (define_test "2020") tests;
