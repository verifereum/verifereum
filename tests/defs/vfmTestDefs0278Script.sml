open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0278";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/set_code_txs_2/gas_diff_pointer_vs_direct_call.json";
val defs = mapi (define_test "0278") tests;
val () = export_theory_no_docs ();
