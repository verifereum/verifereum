open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0235";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/set_code_txs/self_code_on_set_code.json";
val defs = mapi (define_test "0235") tests;
val () = export_theory_no_docs ();
