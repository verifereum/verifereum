Theory vfmTestDefs0701[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/ported_static/stEIP150Specific/call_and_callcode_consume_more_gas_then_transaction_has/call_and_callcode_consume_more_gas_then_transaction_has.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/ported_static/stEIP150Specific/call_and_callcode_consume_more_gas_then_transaction_has/call_and_callcode_consume_more_gas_then_transaction_has.json");
val defs = mapi (define_test "0701") tests;
