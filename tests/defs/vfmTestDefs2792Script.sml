Theory vfmTestDefs2792[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stSystemOperationsTest/suicide_caller/suicide_caller.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stSystemOperationsTest/suicide_caller/suicide_caller.json");
val defs = mapi (define_test "2792") tests;
