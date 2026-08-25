Theory vfmTestDefs2738[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecadd_1-2_0-0_21000_64.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stZeroKnowledge2/ecadd_1-2_0-0_21000_64.json");
val defs = mapi (define_test "2738") tests;
