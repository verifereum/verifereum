Theory vfmTestDefs0653[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/createJS_ExampleContract.json";
val defs = mapi (define_test "0653") tests;
