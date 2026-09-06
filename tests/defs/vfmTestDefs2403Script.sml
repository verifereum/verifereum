Theory vfmTestDefs2403[no_sig_docs]
Libs vfmTestAuxLib vfmTestDefLib
val () = holbuild_extra_deps ["../fixtures/blockchain_tests/for_osaka/prague/eip7702_set_code_tx/set_code_txs/set_code_to_precompile_not_enough_gas_for_precompile_execution.json"];
val tests = json_path_to_tests (vfmTestAuxLib.fixtures_path "blockchain_tests/for_osaka/prague/eip7702_set_code_tx/set_code_txs/set_code_to_precompile_not_enough_gas_for_precompile_execution.json");
val defs = mapi (define_test "2403") tests;
