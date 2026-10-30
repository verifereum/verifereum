Theory vfmTestDefs2726[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_amsterdam/ported_static/stStaticCall/static_return_bounds_oog/static_return_bounds_oog.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_amsterdam/ported_static/stStaticCall/static_return_bounds_oog/static_return_bounds_oog.json");
val defs = mapi (define_test "2726") tests;
