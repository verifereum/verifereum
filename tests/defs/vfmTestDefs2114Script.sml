Theory vfmTestDefs2114[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_Call50000bytesContract50_2.json";
val defs = mapi (define_test "2114") tests;
