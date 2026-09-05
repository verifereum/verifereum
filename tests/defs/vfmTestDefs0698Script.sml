Theory vfmTestDefs0698[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP1153_transientStorage/14_revert_after_nested_staticcall/14_revert_after_nested_staticcall.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP1153_transientStorage/14_revert_after_nested_staticcall/14_revert_after_nested_staticcall.json");
val defs = mapi (define_test "0698") tests;
