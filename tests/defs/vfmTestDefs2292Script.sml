Theory vfmTestDefs2292[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stStaticCall/static_callcode_checkPC.json";
val defs = mapi (define_test "2292") tests;
