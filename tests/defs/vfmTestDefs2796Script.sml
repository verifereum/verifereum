Theory vfmTestDefs2796[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stSystemOperationsTest/suicide_origin/suicide_origin.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stSystemOperationsTest/suicide_origin/suicide_origin.json");
val defs = mapi (define_test "2796") tests;
