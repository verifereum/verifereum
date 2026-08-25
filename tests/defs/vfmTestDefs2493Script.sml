Theory vfmTestDefs2493[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/static/state_tests/stTransactionTest/TransactionSendingToZero.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/static/state_tests/stTransactionTest/TransactionSendingToZero.json");
val defs = mapi (define_test "2493") tests;
