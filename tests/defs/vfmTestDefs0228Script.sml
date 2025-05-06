open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0228";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/set_code_txs/ext_code_on_self_set_code.json";
val defs = mapi (define_test "0228") tests;
val () = export_theory_no_docs ();
