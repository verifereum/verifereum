Theory vfmTestDefs2112[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_Call50000_rip160.json";
val defs = mapi (define_test "2112") tests;
