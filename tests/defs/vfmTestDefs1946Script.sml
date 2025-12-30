Theory vfmTestDefs1946[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stRevertTest/RevertOpcodeMultipleSubCalls.json";
val defs = mapi (define_test "1946") tests;
