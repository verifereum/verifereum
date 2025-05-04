open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs025";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip4844_blobs/blob_txs/blob_type_tx_pre_fork.json";
val defs = mapi (define_state_test "025") tests;
val () = export_theory_no_docs ();
