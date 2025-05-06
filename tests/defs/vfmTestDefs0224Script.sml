open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0224";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/set_code_txs/empty_authorization_list.json";
val defs = mapi (define_test "0224") tests;
val () = export_theory_no_docs ();
