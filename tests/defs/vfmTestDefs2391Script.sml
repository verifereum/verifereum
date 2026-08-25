Theory vfmTestDefs2391[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/CallRecursiveBomb0_OOG_atMaxCallDepth.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stSystemOperationsTest/CallRecursiveBomb0_OOG_atMaxCallDepth.json");
val defs = mapi (define_test "2391") tests;
