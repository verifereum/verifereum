Theory vfmTestDefs2214[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stZeroCallsTest/zero_value_transaction_call_to_non_zero_balance/zero_value_transaction_call_to_non_zero_balance.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stZeroCallsTest/zero_value_transaction_call_to_non_zero_balance/zero_value_transaction_call_to_non_zero_balance.json");
val defs = mapi (define_test "2214") tests;
