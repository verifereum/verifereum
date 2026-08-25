Theory vfmTestDefs0402[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/Cancun/stEIP1153_transientStorage/10_revertUndoesStoreAfterReturn.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/Cancun/stEIP1153_transientStorage/10_revertUndoesStoreAfterReturn.json");
val defs = mapi (define_test "0402") tests;
