Theory vfmTestDefs0405[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/Cancun/stEIP1153_transientStorage/19_oogUndoesTransientStore.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/Cancun/stEIP1153_transientStorage/19_oogUndoesTransientStore.json");
val defs = mapi (define_test "0405") tests;
