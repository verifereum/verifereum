open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0261";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/set_code_txs/set_code_to_sstore_then_sload.json";
val defs = mapi (define_test "0261") tests;
val () = export_theory_no_docs ();
