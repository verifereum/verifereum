open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0223";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/set_code_txs/delegation_clearing.json";
val defs = mapi (define_test "0223") tests;
val () = export_theory_no_docs ();
