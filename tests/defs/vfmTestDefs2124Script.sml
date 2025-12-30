Theory vfmTestDefs2124[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_CallEcrecover0_Gas2999.json";
val defs = mapi (define_test "2124") tests;
