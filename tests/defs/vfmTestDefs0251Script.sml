open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0251";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/set_code_txs/set_code_to_account_deployed_in_same_tx.json";
val defs = mapi (define_test "0251") tests;
val () = export_theory_no_docs ();
