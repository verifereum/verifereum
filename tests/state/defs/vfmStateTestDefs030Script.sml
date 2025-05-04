open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs030";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip4844_blobs/blob_txs/invalid_tx_max_fee_per_blob_gas_state.json";
val defs = mapi (define_state_test "030") tests;
val () = export_theory_no_docs ();
