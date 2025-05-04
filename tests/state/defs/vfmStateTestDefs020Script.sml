open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs020";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip4844_blobs/blob_txs/blob_gas_subtraction_tx.json";
val defs = mapi (define_state_test "020") tests;
val () = export_theory_no_docs ();
