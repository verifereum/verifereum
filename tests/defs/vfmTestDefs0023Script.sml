Theory vfmTestDefs0023[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip1153_tstore/test_tload_after_tstore_is_zero.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip1153_tstore/test_tload_after_tstore_is_zero.json");
val defs = mapi (define_test "0023") tests;
