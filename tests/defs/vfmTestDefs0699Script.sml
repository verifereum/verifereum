Theory vfmTestDefs0699[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP1153_transientStorage/trans_storage_ok/trans_storage_ok.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP1153_transientStorage/trans_storage_ok/trans_storage_ok.json");
val defs = mapi (define_test "0699") tests;
