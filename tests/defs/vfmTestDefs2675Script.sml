Theory vfmTestDefs2675[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecmul_7827-6598_5617_28000_96.json";
val defs = mapi (define_test "2675") tests;
