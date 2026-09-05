Theory vfmTestDefs2328[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/prague/eip6110_deposits/deposits_out_of_gas/deposit_from_contract_transaction_out_of_gas.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/prague/eip6110_deposits/deposits_out_of_gas/deposit_from_contract_transaction_out_of_gas.json");
val defs = mapi (define_test "2328") tests;
