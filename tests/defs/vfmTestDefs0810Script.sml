Theory vfmTestDefs0810[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stCreate2/RevertInCreateInInitCreate2Paris.json";
val defs = mapi (define_test "0810") tests;
