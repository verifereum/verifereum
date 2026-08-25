Theory vfmTestDefs2752[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecadd_6-9_19274124-124124_21000_128.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stZeroKnowledge2/ecadd_6-9_19274124-124124_21000_128.json");
val defs = mapi (define_test "2752") tests;
