Theory vfmTestDefs2174[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CallSha256_4_gas99.json";
val defs = mapi (define_test "2174") tests;
