Theory vfmTestDefs2103[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stTransactionTest/transaction_to_itself/transaction_to_itself.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stTransactionTest/transaction_to_itself/transaction_to_itself.json");
val defs = mapi (define_test "2103") tests;
