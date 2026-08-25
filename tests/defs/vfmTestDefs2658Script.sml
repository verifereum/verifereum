Theory vfmTestDefs2658[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge/ecmul_7827-6598_1456_28000_80.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stZeroKnowledge/ecmul_7827-6598_1456_28000_80.json");
val defs = mapi (define_test "2658") tests;
