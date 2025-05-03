open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs185";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip4844_blobs/blob_txs/invalid_tx_blob_count.json";
val defs = mapi (define_state_test "185") tests;
val () = export_theory_no_docs ();
