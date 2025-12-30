Theory vfmTestDefs2169[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CallSha256_2.json";
val defs = mapi (define_test "2169") tests;
