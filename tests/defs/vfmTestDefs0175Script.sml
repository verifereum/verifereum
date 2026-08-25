Theory vfmTestDefs0175[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/osaka/eip7825_transaction_gas_limit_cap/test_tx_gas_larger_than_block_gas_limit.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/osaka/eip7825_transaction_gas_limit_cap/test_tx_gas_larger_than_block_gas_limit.json");
val defs = mapi (define_test "0175") tests;
