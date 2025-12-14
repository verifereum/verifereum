open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmTestDefs0381";
val tests = json_path_to_tests "../fixtures/blockchain_tests/prague/eip7702_set_code_tx/test_valid_tx_invalid_chain_id.json";
val defs = mapi (define_test "0381") tests;
val () = export_theory_no_docs ();
