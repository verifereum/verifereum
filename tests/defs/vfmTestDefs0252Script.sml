open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0252";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/set_code_txs/set_code_to_precompile_not_enough_gas_for_precompile_execution.json";
val defs = mapi (define_test "0252") tests;
val () = export_theory_no_docs ();
