open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0229";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/set_code_txs/eoa_tx_after_set_code.json";
val defs = mapi (define_test "0229") tests;
val () = export_theory_no_docs ();
