Theory vfmTestDefs2171[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CallSha256_3_postfix0.json";
val defs = mapi (define_test "2171") tests;
