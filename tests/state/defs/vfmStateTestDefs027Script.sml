open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs027";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip4844_blobs/blob_txs/invalid_blob_hash_versioning_single_tx.json";
val defs = mapi (define_state_test "027") tests;
val () = export_theory_no_docs ();
