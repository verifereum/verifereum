Theory vfmTestDefs0756[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP3607/transaction_colliding_with_non_empty_account_calls/transaction_colliding_with_non_empty_account_calls.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP3607/transaction_colliding_with_non_empty_account_calls/transaction_colliding_with_non_empty_account_calls.json");
val defs = mapi (define_test "0756") tests;
