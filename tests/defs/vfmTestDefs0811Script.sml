Theory vfmTestDefs0811[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/RevertOpcodeCreate.json";
val defs = mapi (define_test "0811") tests;
