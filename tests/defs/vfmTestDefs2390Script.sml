Theory vfmTestDefs2390[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stSystemOperationsTest/CallRecursiveBomb0.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stSystemOperationsTest/CallRecursiveBomb0.json");
val defs = mapi (define_test "2390") tests;
