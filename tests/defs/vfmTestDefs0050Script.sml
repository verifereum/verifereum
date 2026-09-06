Theory vfmTestDefs0050[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/cancun/eip1153_tstore/tstorage_clear_after_tx/tstore_clear_after_deployment_tx.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/cancun/eip1153_tstore/tstorage_clear_after_tx/tstore_clear_after_deployment_tx.json");
val defs = mapi (define_test "0050") tests;
