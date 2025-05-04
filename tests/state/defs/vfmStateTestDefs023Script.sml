open HolKernel vfmTestAuxLib vfmTestDefLib;
val () = new_theory "vfmStateTestDefs023";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip4844_blobs/blob_txs/blob_tx_attribute_opcodes.json";
val defs = mapi (define_state_test "023") tests;
val () = export_theory_no_docs ();
