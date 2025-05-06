open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0221";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/set_code_txs/delegation_clearing_failing_tx.json";
val defs = mapi (define_test "0221") tests;
val () = export_theory_no_docs ();
