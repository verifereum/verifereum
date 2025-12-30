Theory vfmTestDefs2666[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecmul_7827-6598_2_28000_128.json";
val defs = mapi (define_test "2666") tests;
