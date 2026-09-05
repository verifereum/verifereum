Theory vfmTestDefs2123[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stTransactionTest/transaction_data_costs652/transaction_data_costs652.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stTransactionTest/transaction_data_costs652/transaction_data_costs652.json");
val defs = mapi (define_test "2123") tests;
