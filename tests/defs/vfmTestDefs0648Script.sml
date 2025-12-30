Theory vfmTestDefs0648[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCallCreateCallCodeTest/createInitFailUndefinedInstruction.json";
val defs = mapi (define_test "0648") tests;
