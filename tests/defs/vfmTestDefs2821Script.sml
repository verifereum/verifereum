Theory vfmTestDefs2821[no_sig_docs]
Libs vfmTestDefLib
val tests = json_path_to_tests "../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecmul_0-3_5616_28000_96_Paris.json";
val defs = mapi (define_test "2821") tests;
