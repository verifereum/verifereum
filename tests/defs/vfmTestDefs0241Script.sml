open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0241";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/set_code_txs/set_code_address_and_authority_warm_state.json";
val defs = mapi (define_test "0241") tests;
val () = export_theory_no_docs ();
