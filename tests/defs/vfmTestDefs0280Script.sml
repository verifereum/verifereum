open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0280";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/set_code_txs_2/pointer_contract_pointer_loop.json";
val defs = mapi (define_test "0280") tests;
val () = export_theory_no_docs ();
