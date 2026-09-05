Theory vfmTestDefs2124[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stTransactionTest/transaction_sending_to_empty/transaction_sending_to_empty.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stTransactionTest/transaction_sending_to_empty/transaction_sending_to_empty.json");
val defs = mapi (define_test "2124") tests;
