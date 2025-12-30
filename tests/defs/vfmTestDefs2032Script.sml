Theory vfmTestDefs2032[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stShift/shr10.json";
val defs = mapi (define_test "2032") tests;
