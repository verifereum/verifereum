Theory vfmTestDefs2651[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecmul_7827-6598_0_28000_64.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stZeroKnowledge/ecmul_7827-6598_0_28000_64.json");
val defs = mapi (define_test "2651") tests;
