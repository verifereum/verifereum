Theory vfmTestDefs2109[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_Call50000_ecrec.json";
val defs = mapi (define_test "2109") tests;
