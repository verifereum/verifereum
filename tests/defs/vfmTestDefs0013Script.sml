Theory vfmTestDefs0013[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/cancun/eip1153_tstore/test_basic_tload_transaction_begin.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/cancun/eip1153_tstore/test_basic_tload_transaction_begin.json");
val defs = mapi (define_test "0013") tests;
