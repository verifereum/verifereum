Theory vfmTestDefs2672[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecmul_7827-6598_5617_21000_128.json";
val defs = mapi (define_test "2672") tests;
