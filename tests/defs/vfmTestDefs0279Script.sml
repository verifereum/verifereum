open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0279";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/set_code_txs_2/pointer_call_followed_by_direct_call.json";
val defs = mapi (define_test "0279") tests;
val () = export_theory_no_docs ();
