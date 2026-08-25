Theory vfmTestDefs2736[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecadd_1-2_0-0_21000_128.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stZeroKnowledge2/ecadd_1-2_0-0_21000_128.json");
val defs = mapi (define_test "2736") tests;
