Theory vfmTestDefs2773[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecmul_0-0_2_28000_96.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stZeroKnowledge2/ecmul_0-0_2_28000_96.json");
val defs = mapi (define_test "2773") tests;
