open HolKernel vfmTestLib;
val () = new_theory "vfmStateTestDefs173";
val tests = state_test_json_path_to_tests "../../fixtures/state_tests/cancun/eip4844_blobs/blobhash_opcode/blobhash_gas_cost.json";
val defs = mapi (define_state_test "173") tests;
val () = export_theory_no_docs ();
