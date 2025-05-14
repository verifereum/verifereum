open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0219";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/set_code_txs/call_into_chain_delegating_set_code.json";
val defs = mapi (define_test "0219") tests;
val () = export_theory_no_docs ();
