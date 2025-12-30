Theory vfmTestDefs2165[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CallRipemd160_4_gas719.json";
val defs = mapi (define_test "2165") tests;
