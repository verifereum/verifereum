Theory vfmTestDefs0028[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip1153_tstore/test_tstore_clear_after_tx.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip1153_tstore/test_tstore_clear_after_tx.json");
val defs = mapi (define_test "0028") tests;
