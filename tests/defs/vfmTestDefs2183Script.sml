Theory vfmTestDefs2183[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CheckOpcodes4.json";
val defs = mapi (define_test "2183") tests;
