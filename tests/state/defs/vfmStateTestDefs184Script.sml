open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs184";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip4844_blobs/blob_txs/blob_tx_attribute_calldata_opcodes.json";
val defs = mapi (define_state_test "184") tests;
val () = export_theory_no_docs ();
