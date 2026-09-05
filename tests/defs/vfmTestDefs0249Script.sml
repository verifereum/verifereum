Theory vfmTestDefs0249[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/osaka/eip7825_transaction_gas_limit_cap/tx_gas_limit/tx_gas_limit_cap_authorized_tx.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/osaka/eip7825_transaction_gas_limit_cap/tx_gas_limit/tx_gas_limit_cap_authorized_tx.json");
val defs = mapi (define_test "0249") tests;
