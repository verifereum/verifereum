Theory vfmTestDefs0649[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/createInitFailUndefinedInstruction2.json";
val defs = mapi (define_test "0649") tests;
