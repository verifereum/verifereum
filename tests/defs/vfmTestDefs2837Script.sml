Theory vfmTestDefs2837[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stZeroKnowledge2/ecmul_1-2_0_21000_96.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stZeroKnowledge2/ecmul_1-2_0_21000_96.json");
val defs = mapi (define_test "2837") tests;
