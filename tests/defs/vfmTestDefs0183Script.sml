Theory vfmTestDefs0183[no_sig_docs]
Libs vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/osaka/eip7825_transaction_gas_limit_cap/test_tx_gas_limit_cap_subcall_context.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/osaka/eip7825_transaction_gas_limit_cap/test_tx_gas_limit_cap_subcall_context.json");
val defs = mapi (define_test "0183") tests;
