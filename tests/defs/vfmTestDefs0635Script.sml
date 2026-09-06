Theory vfmTestDefs0635[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stCreate2/revert_depth_create2_oog/revert_depth_create2_oog.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stCreate2/revert_depth_create2_oog/revert_depth_create2_oog.json");
val defs = mapi (define_test "0635") tests;
