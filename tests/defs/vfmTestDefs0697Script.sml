Theory vfmTestDefs0697[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP1153_transientStorage/10_revert_undoes_store_after_return/10_revert_undoes_store_after_return.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP1153_transientStorage/10_revert_undoes_store_after_return/10_revert_undoes_store_after_return.json");
val defs = mapi (define_test "0697") tests;
