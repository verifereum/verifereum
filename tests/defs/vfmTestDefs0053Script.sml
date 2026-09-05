Theory vfmTestDefs0053[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/cancun/eip1153_tstore/tstorage_create_contexts/tstore_rollback_on_failed_create.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/cancun/eip1153_tstore/tstorage_create_contexts/tstore_rollback_on_failed_create.json");
val defs = mapi (define_test "0053") tests;
