open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0267";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/set_code_txs/set_code_using_valid_synthetic_signatures.json";
val defs = mapi (define_test "0267") tests;
val () = export_theory_no_docs ();
