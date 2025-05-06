open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0266";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/set_code_txs/tx_into_self_delegating_set_code.json";
val defs = mapi (define_test "0266") tests;
val () = export_theory_no_docs ();
