open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs179";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip4844_blobs/blob_txs/blob_tx_attribute_value_opcode.json";
val defs = mapi (define_state_test "179") tests;
val () = export_theory_no_docs ();
