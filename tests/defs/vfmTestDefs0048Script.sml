Theory vfmTestDefs0048[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/cancun/eip1153_tstore/tstorage/tload_after_tstore_is_zero.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/cancun/eip1153_tstore/tstorage/tload_after_tstore_is_zero.json");
val defs = mapi (define_test "0048") tests;
