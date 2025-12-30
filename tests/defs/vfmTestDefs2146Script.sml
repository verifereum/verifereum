Theory vfmTestDefs2146[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CallIdentity_4_gas17.json";
val defs = mapi (define_test "2146") tests;
