open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0233";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/set_code_txs/nonce_validity.json";
val defs = mapi (define_test "0233") tests;
val () = export_theory_no_docs ();
